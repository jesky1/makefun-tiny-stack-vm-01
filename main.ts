// Tiny stack VM: one program answers a whole set of tiny-stack-vm-01 instances.
// Reads MAKEFUN_INPUT_DIR/<id>/{program,input}.bin, writes
// MAKEFUN_OUTPUT_DIR/<id>/{stdout.bin,exit.txt} for every id it finds.
// ISA: kit program/generator/subject/ISA.md (vm.mjs beside it is the rule).
// Values wrap at 32 bits; a trap ends the program at once, keeping prior output.
import {mkdirSync, readdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';

// Per-opcode table: [byte, immediate bytes, pops, pushes].
const IM = new Uint8Array(256), PO = new Uint8Array(256), PU = new Uint8Array(256), KN = new Uint8Array(256);
for (const [o, i, p, u] of [
  [0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],
  [16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],
  [23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],
  [30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],
  [51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0],
]) { IM[o] = i; PO[o] = p; PU[o] = u; KN[o] = 1; }

// Runs one program on its input; returns [output bytes, exit code 0..255].
function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const n = p.length;
  const D = new Int32Array(256); // data stack
  const C = new Int32Array(64);  // call stack (return addresses)
  const M = new Int32Array(256); // memory, starts zeroed
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const end = (e: number): [Uint8Array, number] => [out.subarray(0, ol), e];
  for (;;) {
    if (st === 1000000) return end(10); // step limit
    if (pc < 0 || pc >= n) return end(9); // pc outside the program
    const op = p[pc];
    if (!KN[op]) return end(5); // unknown opcode
    const im = IM[op];
    if (pc + im >= n) return end(9); // immediate cut off by the end
    st++;
    const nx = pc + 1 + im; // address of the next instruction
    if (sp < PO[op]) return end(2); // stack underflow
    if (sp - PO[op] + PU[op] > 256) return end(3); // stack overflow
    pc = nx;
    switch (op) {
      case 0: return end(0); // HALT
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break; // PUSH32 LE
      case 3: sp--; break; // POP
      case 4: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 6: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 23: D[sp - 1] = -D[sp - 1] | 0; break; // NEG
      case 27: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 48: case 49: case 50: { // JMP / JZ / JNZ: signed 16-bit offset from nx
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51: // CALL: unsigned 16-bit target
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52: // RET
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 64: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: { // STORE (v addr --): addr is the top
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a > 255) return end(6);
        sp -= 2; M[a] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII, no newline
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN (-1 when exhausted)
      case 83: return end(D[--sp] & 255); // EXIT: low byte
      default: { // binary ops 0x10-0x16, 0x18-0x1a, 0x1c-0x1e, 0x20-0x22 (a b -- r)
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op >= 19 && op <= 22 && b === 0) return end(4); // DIV/MOD/DIVU/MODU by zero
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) r = a === -2147483648 && b === -1 ? a : (a / b) | 0; // DIV, toward zero
        else if (op === 20) r = b === -1 ? 0 : (a % b) | 0; // MOD, sign of a
        else if (op === 21) r = Math.floor((a >>> 0) / (b >>> 0)) | 0; // DIVU
        else if (op === 22) r = ((a >>> 0) % (b >>> 0)) | 0; // MODU
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31); // SHL
        else if (op === 29) r = a >> (b & 31); // SHR, arithmetic
        else if (op === 30) r = (a >>> (b & 31)) | 0; // SHRU, logical
        else if (op === 32) r = a === b ? 1 : 0; // EQ
        else if (op === 33) r = a < b ? 1 : 0; // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        sp -= 2; D[sp++] = r;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [o, e] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), o);
  writeFileSync(join(O, id, 'exit.txt'), e + '\n');
}
