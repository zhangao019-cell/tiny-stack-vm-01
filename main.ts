import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode tables, indexed by opcode byte (0x00..0x53), one digit each:
// NP = values popped, NQ = values pushed, NI = immediate bytes. Derived from ISA.md.
const NP = "000112230000000022222221222122202220000000000000011000000000000012000000000000001101";
const NQ = "011022330000000011111111111111101110000000000000000000000000000010000000000000000010";
const NI = "014000000000000000000000000000000000000000000000222200000000000000000000000000000000";

function exec(prog: Uint8Array, input: Uint8Array): { out: number[]; code: number } {
  const d = new Int32Array(256);
  let sp = 0;
  const cs = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const out: number[] = [];
  let pc = 0;
  let ip = 0;
  let n = 0;
  const trap = (code: number) => ({ out, code });
  for (;;) {
    if (n === 1000000) return trap(10);
    if (pc < 0 || pc >= prog.length) return trap(9);
    const op = prog[pc];
    const imm = NI.charCodeAt(op) - 48;
    const known = op === 0x00 || imm > 0 || NP.charCodeAt(op) > 48 || NQ.charCodeAt(op) > 48 || op === 0x34 || op === 0x52;
    if (!known) return trap(5);
    if (pc + imm >= prog.length) return trap(9);
    n++;
    const nx = pc + 1 + imm;
    const pops = NP.charCodeAt(op) - 48;
    const pushes = NQ.charCodeAt(op) - 48;
    if (sp < pops) return trap(2);
    if (sp - pops + pushes > 256) return trap(3);
    pc = nx;
    const rel = op >= 0x30 && op <= 0x32 ? (((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16) : 0;
    switch (op) {
      case 0x00: return { out, code: 0 };
      case 0x01: d[sp++] = (prog[nx - 1] << 24) >> 24; break;
      case 0x02: d[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: d[sp] = d[sp - 1]; sp++; break;
      case 0x05: { const t = d[sp - 1]; d[sp - 1] = d[sp - 2]; d[sp - 2] = t; break; }
      case 0x06: d[sp] = d[sp - 2]; sp++; break;
      case 0x07: { const a = d[sp - 3]; d[sp - 3] = d[sp - 2]; d[sp - 2] = d[sp - 1]; d[sp - 1] = a; break; }
      case 0x10: { const b = d[--sp]; d[sp - 1] = (d[sp - 1] + b) | 0; break; }
      case 0x11: { const b = d[--sp]; d[sp - 1] = (d[sp - 1] - b) | 0; break; }
      case 0x12: { const b = d[--sp]; d[sp - 1] = Math.imul(d[sp - 1], b); break; }
      case 0x13: { const b = d[--sp]; if (b === 0) return trap(4); d[sp - 1] = d[sp - 1] === -2147483648 && b === -1 ? -2147483648 : (d[sp - 1] / b) | 0; break; }
      case 0x14: { const b = d[--sp]; if (b === 0) return trap(4); d[sp - 1] = b === -1 ? 0 : (d[sp - 1] % b) | 0; break; }
      case 0x15: { const b = d[--sp]; if (b === 0) return trap(4); d[sp - 1] = Math.floor((d[sp - 1] >>> 0) / (b >>> 0)) | 0; break; }
      case 0x16: { const b = d[--sp]; if (b === 0) return trap(4); d[sp - 1] = ((d[sp - 1] >>> 0) % (b >>> 0)) | 0; break; }
      case 0x17: d[sp - 1] = -d[sp - 1] | 0; break;
      case 0x18: { const b = d[--sp]; d[sp - 1] = d[sp - 1] & b; break; }
      case 0x19: { const b = d[--sp]; d[sp - 1] = d[sp - 1] | b; break; }
      case 0x1a: { const b = d[--sp]; d[sp - 1] = d[sp - 1] ^ b; break; }
      case 0x1b: d[sp - 1] = ~d[sp - 1]; break;
      case 0x1c: { const b = d[--sp]; d[sp - 1] = d[sp - 1] << (b & 31); break; }
      case 0x1d: { const b = d[--sp]; d[sp - 1] = d[sp - 1] >> (b & 31); break; }
      case 0x1e: { const b = d[--sp]; d[sp - 1] = (d[sp - 1] >>> (b & 31)) | 0; break; }
      case 0x20: { const b = d[--sp]; d[sp - 1] = d[sp - 1] === b ? 1 : 0; break; }
      case 0x21: { const b = d[--sp]; d[sp - 1] = d[sp - 1] < b ? 1 : 0; break; }
      case 0x22: { const b = d[--sp]; d[sp - 1] = (d[sp - 1] >>> 0) < (b >>> 0) ? 1 : 0; break; }
      case 0x30: pc = nx + rel; break;
      case 0x31: { const v = d[--sp]; if (v === 0) pc = nx + rel; break; }
      case 0x32: { const v = d[--sp]; if (v !== 0) pc = nx + rel; break; }
      case 0x33: if (cp === 64) return trap(7); cs[cp++] = nx; pc = prog[nx - 2] | (prog[nx - 1] << 8); break;
      case 0x34: if (cp === 0) return trap(8); pc = cs[--cp]; break;
      case 0x40: { const a = d[sp - 1]; if (a < 0 || a >= 256) return trap(6); d[sp - 1] = mem[a]; break; }
      case 0x41: { const a = d[sp - 1]; const v = d[sp - 2]; if (a < 0 || a >= 256) return trap(6); sp -= 2; mem[a] = v; break; }
      case 0x50: { const s = String(d[sp - 1]); if (out.length + s.length > 65536) return trap(11); sp--; for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i)); break; }
      case 0x51: if (out.length + 1 > 65536) return trap(11); out.push(d[--sp] & 255); break;
      case 0x52: d[sp++] = ip < input.length ? input[ip++] : -1; break;
      case 0x53: return { out, code: d[--sp] & 255 };
      default: return trap(5);
    }
  }
}

const IND = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTD = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IND).sort()) {
  const r = exec(new Uint8Array(readFileSync(join(IND, id, 'program.bin'))), new Uint8Array(readFileSync(join(IND, id, 'input.bin'))));
  mkdirSync(join(OUTD, id), { recursive: true });
  writeFileSync(join(OUTD, id, 'stdout.bin'), Uint8Array.from(r.out));
  writeFileSync(join(OUTD, id, 'exit.txt'), `${r.code}\n`);
}
