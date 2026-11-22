// Tiny stack VM: a complete interpreter for make.fun's tiny stack ISA v1
// (ISA.md in the kit). One run answers a whole set: it reads
// /input/<id>/{program,input}.bin and writes /output/<id>/{stdout.bin,exit.txt}.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const n = p.length;
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const done = (code: number): [Uint8Array, number] => [out.subarray(0, ol), code];
  const nd = (k: number) => { if (sp < k) throw 2; }; // stack underflow
  const ov = () => { if (sp >= 256) throw 3; }; // stack overflow
  try {
    for (;;) {
      if (st === 1e6) throw 10; // step limit
      if (pc < 0 || pc >= n) throw 9; // pc outside the program
      const op = p[pc];
      if (op === 0) { // HALT
        st++;
        return done(0);
      } else if (op === 1) { // PUSH8, signed 8-bit, sign-extended
        if (pc + 1 >= n) throw 9;
        st++; ov();
        D[sp++] = (p[pc + 1] << 24) >> 24;
        pc += 2;
      } else if (op === 2) { // PUSH32, signed 32-bit, little-endian
        if (pc + 4 >= n) throw 9;
        st++; ov();
        D[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24);
        pc += 5;
      } else if (op === 3) { // POP
        st++; nd(1); sp--; pc++;
      } else if (op === 4 || op === 6) { // DUP / OVER
        st++; nd(op === 4 ? 1 : 2); ov();
        D[sp] = D[sp - (op === 4 ? 1 : 2)];
        sp++; pc++;
      } else if (op === 5) { // SWAP
        st++; nd(2);
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        pc++;
      } else if (op === 7) { // ROT: (a b c -- b c a)
        st++; nd(3);
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        pc++;
      } else if (op === 0x17 || op === 0x1b) { // NEG / NOT
        st++; nd(1);
        D[sp - 1] = op === 0x17 ? (-D[sp - 1]) | 0 : ~D[sp - 1];
        pc++;
      } else if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b && op !== 0x1f) {
        // Two-operand arithmetic: (a b -- r), b is the top.
        st++; nd(2);
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0; // ADD, wraps
        else if (op === 0x11) r = (a - b) | 0; // SUB, wraps
        else if (op === 0x12) r = Math.imul(a, b); // MUL, low 32 bits
        else if (op === 0x13) { // DIV, truncates toward zero
          if (b === 0) throw 4;
          r = (a / b) | 0; // -2147483648 / -1 wraps to itself via |0
        } else if (op === 0x14) { // MOD, sign of a
          if (b === 0) throw 4;
          r = (a % b) | 0; // x % -1 is 0
        } else if (op === 0x15) { // DIVU, unsigned
          if (b === 0) throw 4;
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) { // MODU, unsigned
          if (b === 0) throw 4;
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b; // AND
        else if (op === 0x19) r = a | b; // OR
        else if (op === 0x1a) r = a ^ b; // XOR
        else if (op === 0x1c) r = a << b; // SHL, count masked to 5 bits by JS
        else if (op === 0x1d) r = a >> b; // SHR, arithmetic
        else if (op === 0x1e) r = (a >>> b) | 0; // SHRU, logical, read back signed
        else if (op === 0x20) r = a === b ? 1 : 0; // EQ
        else if (op === 0x21) r = a < b ? 1 : 0; // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        D[sp - 2] = r;
        sp--; pc++;
      } else if (op === 0x30 || op === 0x31 || op === 0x32) { // JMP / JZ / JNZ
        if (pc + 2 >= n) throw 9;
        st++;
        const rel = ((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16; // signed 16-bit
        const next = pc + 3;
        let take = op === 0x30;
        if (op !== 0x30) {
          nd(1);
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        pc = take ? next + rel : next;
      } else if (op === 0x33) { // CALL: push next address, jump absolute
        if (pc + 2 >= n) throw 9;
        st++;
        if (cp === 64) throw 7;
        C[cp++] = pc + 3;
        pc = p[pc + 1] | (p[pc + 2] << 8);
      } else if (op === 0x34) { // RET
        st++;
        if (cp === 0) throw 8;
        pc = C[--cp];
      } else if (op === 0x40) { // LOAD
        st++; nd(1);
        const a = D[sp - 1];
        if (a < 0 || a > 255) throw 6;
        D[sp - 1] = M[a];
        pc++;
      } else if (op === 0x41) { // STORE: (v addr --)
        st++; nd(2);
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a > 255) throw 6;
        sp -= 2;
        M[a] = v;
        pc++;
      } else if (op === 0x50) { // PRINT: decimal ASCII, no newline
        st++; nd(1);
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) throw 11; // writes nothing
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        pc++;
      } else if (op === 0x51) { // PUTC: one byte, v AND 255
        st++; nd(1);
        if (ol + 1 > 65536) throw 11;
        out[ol++] = D[--sp] & 255;
        pc++;
      } else if (op === 0x52) { // IN: next input byte, -1 when used up
        st++; ov();
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        pc++;
      } else if (op === 0x53) { // EXIT: code v AND 255
        st++; nd(1);
        return done(D[--sp] & 255);
      } else {
        throw 5; // unknown opcode
      }
    }
  } catch (e) {
    return done(typeof e === 'number' ? e : 1);
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let out: Uint8Array, code: number;
  try {
    [out, code] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  } catch {
    out = new Uint8Array(0); // a bug in one instance must not kill the whole set
    code = 1;
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
