import {
  ASSERT,
  getTerm,
  TRACE,
  TRACE_SILENT,
  THROW,
} from '../../fdlib/src/helpers';
import {
  domain__debug,
} from '../../fdlib/src/domain';

// BODY_START

let ml_opcodeCounter = 0;

// note: all ops accept vars and literals
// - a var is signified by a V
// - an 8bit literal signified by 8
// - a 16bit literal signified by F

const ML_START = ml_opcodeCounter++;

const ML_ALL = ml_opcodeCounter++;  // &     all()
const ML_DIFF = ml_opcodeCounter++; // !=    diff()
const ML_IMP = ml_opcodeCounter++;  // ->                (logical implication)
const ML_LT = ml_opcodeCounter++;   // <
const ML_LTE = ml_opcodeCounter++;  // <=
const ML_NALL = ml_opcodeCounter++; // !&    nall()
const ML_NIMP = ml_opcodeCounter++; // !(->)
const ML_NONE = ml_opcodeCounter++; // ==0   none()
const ML_SAME = ml_opcodeCounter++; // ==    same()
const ML_SOME = ml_opcodeCounter++; // |     some()
const ML_XNOR = ml_opcodeCounter++; // !^    xnor()
const ML_XOR = ml_opcodeCounter++;  // ^     xor()

const ML_ISALL = ml_opcodeCounter++;
const ML_ISDIFF = ml_opcodeCounter++;
const ML_ISLT = ml_opcodeCounter++;
const ML_ISLTE = ml_opcodeCounter++;
const ML_ISNALL = ml_opcodeCounter++;
const ML_ISNONE = ml_opcodeCounter++;
const ML_ISSAME = ml_opcodeCounter++;
const ML_ISSOME = ml_opcodeCounter++;

const ML_SUM = ml_opcodeCounter++;
const ML_PRODUCT = ml_opcodeCounter++;
const ML_MINUS = ml_opcodeCounter++;
const ML_DIV = ml_opcodeCounter++;

const ML_NOLEAF = ml_opcodeCounter++;
const ML_NOBOOL = ml_opcodeCounter++;
const ML_JMP = ml_opcodeCounter++;
const ML_JMP32 = ml_opcodeCounter++;
const ML_NOOP = ml_opcodeCounter++;
const ML_NOOP2 = ml_opcodeCounter++;
const ML_NOOP3 = ml_opcodeCounter++;
const ML_NOOP4 = ml_opcodeCounter++;
const ML_STOP = 0xff;

ASSERT(ml_opcodeCounter < 0xff, 'All opcodes are 8bit');
ASSERT(ML_START === 0);
ASSERT(ML_STOP === 0xff);

const SIZEOF_V = 1 + 2; // 16bit
const SIZEOF_W = 1 + 4; // 32bit
const SIZEOF_VV = 1 + 2 + 2;
const SIZEOF_VVV = 1 + 2 + 2 + 2;
const SIZEOF_C = 1 + 2; // + 2*count
const SIZEOF_C_2 = SIZEOF_C + 2 * 2; // fixed 2 var without result
const SIZEOF_CR_2 = SIZEOF_C + 2 * 2 + 2; // fixed 2 var with result

const OFFSET_C_A = SIZEOF_C;
const OFFSET_C_B = SIZEOF_C + 2;
const OFFSET_C_C = SIZEOF_C + 4;
const OFFSET_C_R = OFFSET_C_C;

let ml_typeCounter = 0;
const ML_NO_ARGS = ++ml_typeCounter;
const ML_V = ++ml_typeCounter;
const ML_W = ++ml_typeCounter;
const ML_VV = ++ml_typeCounter;
const ML_VVV = ++ml_typeCounter;
const ML_C = ++ml_typeCounter;
const ML_C_2 = ++ml_typeCounter;
const ML_CR = ++ml_typeCounter;
const ML_C8R = ++ml_typeCounter;

function ml_sizeof(ml, offset, op) {
  switch (op) {
    case ML_IMP:
    case ML_LT:
    case ML_LTE:
    case ML_NIMP:
    case ML_XOR:
      ASSERT(ml_dec16(ml, offset + 1) === 2);
      return SIZEOF_C_2; // always

    case ML_START:
      return 1;

    case ML_ISLT:
    case ML_ISLTE:
    case ML_MINUS:
    case ML_DIV:
      return SIZEOF_VVV;

    case ML_ALL:
    case ML_DIFF:
    case ML_NALL:
    case ML_NONE:
    case ML_SAME:
    case ML_SOME:
    case ML_XNOR:
      if (ml && offset >= 0) return SIZEOF_C + _dec16(ml, offset + 1) * 2;
      return -1;

    case ML_ISALL:
    case ML_ISDIFF:
    case ML_ISNALL:
    case ML_ISNONE:
    case ML_ISSAME:
    case ML_ISSOME:
      if (ml && offset >= 0) return SIZEOF_C + _dec16(ml, offset + 1) * 2 + 2;
      ASSERT(false, 'dont allow this');
      return -1;

    case ML_SUM:
    case ML_PRODUCT:
      if (ml && offset >= 0) return SIZEOF_C + _dec16(ml, offset + 1) * 2 + 2;
      ASSERT(false, 'dont allow this');
      return -1;

    case ML_NOBOOL:
    case ML_NOLEAF:
      return SIZEOF_V;
    case ML_JMP:
      return SIZEOF_V + _dec16(ml, offset + 1);
    case ML_JMP32:
      return SIZEOF_W + _dec32(ml, offset + 1);
    case ML_NOOP:
      return 1;
    case ML_NOOP2:
      return 2;
    case ML_NOOP3:
      return 3;
    case ML_NOOP4:
      return 4;
    case ML_STOP:
      return 1;
    default:
      getTerm().log('(ml) unknown op', op, ' at', offset);
      TRACE('(ml_sizeof) unknown op: ' + ml[offset], ' at', offset);
      THROW('(ml_sizeof) unknown op: ' + ml[offset], ' at', offset);
  }
}

function _dec8(ml, pc) {
  return ml[pc];
}
function ml_dec8(ml, pc) {
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);
  let num = _dec8(ml, pc);
  TRACE_SILENT(' . dec8pc decoding', num, 'from', pc);

  return num;
}

function _dec16(ml, pc) {
  return (ml[pc++] << 8) | ml[pc];
}
function ml_dec16(ml, pc) {
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);

  let n = _dec16(ml, pc);

  TRACE_SILENT(' . dec16pc decoding', ml[pc] << 8, 'from', pc, 'and', ml[pc + 1], 'from', pc + 1, '-->', n);
  return n;
}

function _dec32(ml, pc) {
  return (ml[pc++] << 24) | (ml[pc++] << 16) | (ml[pc++] << 8) | ml[pc];
}
function ml_dec32(ml, pc) {
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);

  let n = _dec32(ml, pc);

  TRACE_SILENT(' . dec32pc decoding', ml[pc], ml[pc + 1], ml[pc + 2], ml[pc + 3], '( x' + ml[pc].toString(16) + ml[pc + 1].toString(16) + ml[pc + 2].toString(16) + ml[pc + 3].toString(16), ') from', pc, '-->', n);
  return n;
}

function ml_enc8(ml, pc, num) {
  TRACE_SILENT(' . enc8(' + pc + ', ' + num + '/x' + (num && num.toString(16)) + ') at', pc, ' ');
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);
  ASSERT(typeof num === 'number', 'Encoding numbers', num);
  ASSERT(num >= 0 && num <= 0xff, 'Only encode 8bit values', num, '0x' + num.toString(16));
  ASSERT(num >= 0, 'only expecting non-negative nums', num);

  ml[pc] = num;
}

function ml_enc16(ml, pc, num) {
  TRACE_SILENT(' - enc16(' + pc + ', ' + num + '/x' + num.toString(16) + ')', (num >> 8) & 0xff, 'at', pc, 'and', num & 0xff, 'at', pc + 1);
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);
  ASSERT(typeof num === 'number', 'Encoding numbers');
  ASSERT(num <= 0xffff, 'implement 32bit index support if this breaks', num);
  ASSERT(num >= 0, 'only expecting non-negative nums', num);

  ml[pc++] = (num >> 8) & 0xff;
  ml[pc] = num & 0xff;
}

function ml_enc32(ml, pc, num) {
  TRACE_SILENT(' - enc32(' + pc + ', ' + num + '/x' + num.toString(16) + ')', ml[pc], ml[pc + 1], ml[pc + 2], ml[pc + 3], '( x' + ml[pc].toString(16) + ml[pc + 1].toString(16) + ml[pc + 2].toString(16) + ml[pc + 3].toString(16), ') at', pc + 1);
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);
  ASSERT(typeof num === 'number', 'Encoding numbers');
  ASSERT(num <= 0xffffffff, 'implement 64bit index support if this breaks', num);
  ASSERT(num >= 0, 'only expecting non-negative nums', num);

  ml[pc++] = (num >> 24) & 0xff;
  ml[pc++] = (num >> 16) & 0xff;
  ml[pc++] = (num >> 8) & 0xff;
  ml[pc] = num & 0xff;
}

function ml_eliminate(ml, offset, sizeof) {
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array', ml);
  //ASSERT(ml_validateSkeleton(ml, 'ml_eliminate; before'));
  TRACE(' - ml_eliminate: eliminating constraint at', offset, 'with size =', sizeof, ', ml=', ml.length < 50 ? ml.join(' ') : '<BIG>');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < ml.length, 'valid offset required');
  ASSERT(typeof sizeof === 'number' && sizeof >= 0, 'valid sizeof required');
  ASSERT(sizeof === ml_getOpSizeSlow(ml, offset), 'sizeof should match size of op at offset', sizeof, ml_getOpSizeSlow(ml, offset), ml__debug(ml, offset, 1, undefined, true, true)); // maybe we should move to do this permanently "slow"
  ml_compileJumpSafe(ml, offset, sizeof);
  TRACE('    - after ml_eliminate:', ml.length < 50 ? ml.join(' ') : '<trunced>');
  ASSERT(ml_validateSkeleton(ml, 'ml_eliminate; after'));
}

function ml_compileJumpAndConsolidate(ml, offset, len) {
  TRACE('  - ml_jump: offset = ', offset, 'len = ', len);

  switch (ml[offset + len]) {
    case ML_NOOP:
      TRACE('  - jmp target is another jmp (noop), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + 1);
    case ML_NOOP2:
      TRACE('  - jmp target is another jmp (noop2), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + 2);
    case ML_NOOP3:
      TRACE('  - jmp target is another jmp (noop3), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + 3);
    case ML_NOOP4:
      TRACE('  - jmp target is another jmp (noop4), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + 4);
    case ML_JMP:
      let jmplen = ml_dec16(ml, offset + len + 1);
      ASSERT(jmplen > 0, 'dont think zero is a valid jmp len');
      ASSERT(jmplen <= 0xffff, 'oob');
      TRACE('  - jmp target is another jmp (len =', SIZEOF_V + jmplen, '), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + SIZEOF_V + jmplen);
    case ML_JMP32:
      let jmplen32 = ml_dec32(ml, offset + len + 1);
      ASSERT(jmplen32 > 0, 'dont think zero is a valid jmp len');
      ASSERT(jmplen32 <= 0xffffffff, 'oob');
      TRACE('  - jmp target is a jmp32 (len =', SIZEOF_W + jmplen32, '), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + SIZEOF_W + jmplen32);
  }

  ml_compileJumpSafe(ml, offset, len);
}

function ml_compileJumpSafe(ml, offset, len) {
  switch (len) {
    case 0:
      return THROW('this is a bug');
    case 1:
      TRACE('  - compiling a NOOP');
      return ml_enc8(ml, offset, ML_NOOP);
    case 2:
      TRACE('  - compiling a NOOP2');
      return ml_enc8(ml, offset, ML_NOOP2);
    case 3:
      TRACE('  - compiling a NOOP3');
      return ml_enc8(ml, offset, ML_NOOP3);
    case 4:
      TRACE('  - compiling a NOOP4');
      return ml_enc8(ml, offset, ML_NOOP4);
    default:
      if (len < 0xffff) {
        TRACE('  - compiling a ML_JMP of', len, '(compiles', len - SIZEOF_V, 'because SIZEOF_V=', SIZEOF_V, ')');
        ml_enc8(ml, offset, ML_JMP);
        ml_enc16(ml, offset + 1, len - SIZEOF_V);
      } else {
        TRACE('  - compiling a ML_JMP32 of', len, '(compiles', len - SIZEOF_W, 'because SIZEOF_W=', SIZEOF_W, ')');
        ml_enc8(ml, offset, ML_JMP32);
        ml_enc32(ml, offset + 1, len - SIZEOF_W);
      }
  }
  //ASSERT(ml_validateSkeleton(ml, 'ml_jump; after'));
}

function ml_pump(ml, offset, from, to, len) {
  TRACE(' - pumping from', offset + from, 'to', offset + to, '(len=', len, ')');
  let fromOffset = offset + from;
  let toOffset = offset + to;
  for (let i = 0; i < len; ++i) {
    TRACE(' - pump', fromOffset, toOffset, '(1)');
    ml[fromOffset++] = ml[toOffset++];
  }
}

function ml_countConstraints(ml) {
  let pc = 0;
  let constraints = 0;

  while (pc < ml.length) {
    let pcStart = pc;
    let op = ml[pc];
    switch (op) {
      case ML_START:
        if (pc !== 0) return THROW('mlConstraints: zero op @', pcStart, 'Uint8Array(' + ml.toString('hex').replace(/(..)/g, '$1 ') + ')');
        ++pc;
        break;

      case ML_STOP:
        return constraints;

      case ML_NOOP:
        ++pc;
        break;
      case ML_NOOP2:
        pc += 2;
        break;
      case ML_NOOP3:
        pc += 3;
        break;
      case ML_NOOP4:
        pc += 4;
        break;
      case ML_JMP:
        pc += SIZEOF_V + _dec16(ml, pc + 1);
        break;
      case ML_JMP32:
        pc += SIZEOF_W + _dec32(ml, pc + 1);
        break;

      default:
        let size = ml_sizeof(ml, pc, op); // throws if op is unknown
        ++constraints;
        pc += size;
    }
  }

  THROW('ML OOB');
}

function ml_hasConstraint(ml) {
  // technically this should be cheap; either the first
  // op is a constraint or it's a jump directly to stop.
  // (all jumps should be consolidated)
  let pc = 0;

  while (pc < ml.length) {
    switch (ml[pc]) {
      case ML_START:
        if (pc !== 0) return ml_throw('oops');
        ++pc;
        break;

      case ML_STOP:
        return false;

      case ML_NOOP:
        ++pc;
        break;
      case ML_NOOP2:
        pc += 2;
        break;
      case ML_NOOP3:
        pc += 3;
        break;
      case ML_NOOP4:
        pc += 4;
        break;
      case ML_JMP:
        pc += SIZEOF_V + _dec16(ml, pc + 1);
        break;
      case ML_JMP32:
        pc += SIZEOF_W + _dec32(ml, pc + 1);
        break;

      default:
        return true;
    }
  }

  THROW('ML OOB');
}

function ml_c2vv(ml, offset, argCount, opCode, indexA, indexB) {
  // "count without result" (diff, some, nall, etc)
  TRACE(' -| ml_c2vv | from', offset, ', argCount=', argCount, 'to op', ml__opName(opCode), ', args:', indexA, indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) >= SIZEOF_VV, 'the c2 should fit the existing space entirely');
  ASSERT(ml_dec16(ml, offset + 1) === argCount, 'argcount should match');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, indexA);
  ml_enc16(ml, offset + 3, indexB);

  let oldLen = SIZEOF_C + argCount * 2;
  if (SIZEOF_VV < oldLen) ml_compileJumpSafe(ml, offset + SIZEOF_VV, oldLen - SIZEOF_VV);
  ASSERT(ml_validateSkeleton(ml, 'ml_c2vv'));
}

function ml_c2c2(ml, offset, argCount, opCode, indexA, indexB) {
  // "count without result" (diff, some, nall, etc) to same count type with 2 args without result
  TRACE(' -| ml_c2c2 | from', offset, ', argCount=', argCount, 'to op', ml__opName(opCode), ', args:', indexA, indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) >= SIZEOF_C_2, 'the c2 should fit the existing space entirely');
  ASSERT(ml_dec16(ml, offset + 1) === argCount, 'argcount should match');
  ASSERT(argCount > 1, 'this fails with count<2 because theres not enough space');

  //ASSERT(ml_validateSkeleton(ml, 'ml_c2c2-before'));

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, 2);
  ml_enc16(ml, offset + OFFSET_C_A, indexA);
  ml_enc16(ml, offset + OFFSET_C_B, indexB);

  let oldLen = SIZEOF_C + argCount * 2;
  if (SIZEOF_C_2 < oldLen) ml_compileJumpSafe(ml, offset + SIZEOF_C_2, oldLen - SIZEOF_C_2);
  ASSERT(ml_validateSkeleton(ml, 'ml_c2c2'));
}

function ml_cx2cx(ml, offset, argCount, opCode, args) {
  TRACE(' -| ml_cx2cx | from', offset, 'was argCount=', argCount, 'to op', ml__opName(opCode), 'with args', args, ', new size should be', SIZEOF_C + args.length * 2);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof argCount === 'number' && argCount > 0 && argCount < ml.length, 'valid argCount', argCount);
  ASSERT(args instanceof Array, 'args is list of indexes', args);
  ASSERT(argCount === args.length, 'this function excepts to morph one count op into another count op of the same size', argCount, args.length, args);

  args.sort((a, b) => a - b); // compile args sorted
  let opSize = SIZEOF_C + argCount * 2;
  ASSERT((argCount === args.length) === (ml_getOpSizeSlow(ml, offset) === opSize), 'if same argcount then same size');
  ASSERT(ml_getOpSizeSlow(ml, offset) === opSize, 'the should fit the existing space entirely');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, argCount);
  for (let i = 0; i < argCount; ++i) {
    ml_enc16(ml, offset + SIZEOF_C + i * 2, args[i]);
  }

  ASSERT(ml_validateSkeleton(ml, 'ml_cx2cx'));
}

function ml_any2c(ml, offset, oldSizeof, opCode, args) {
  TRACE(' -| ml_any2c | from', offset, 'was len=', oldSizeof, 'to op', ml__opName(opCode), 'with args', args, ', new size should be', SIZEOF_C + args.length * 2);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof oldSizeof === 'number' && offset > 0 && offset < ml.length, 'valid oldSizeof', oldSizeof);
  ASSERT(args instanceof Array, 'args is list of indexes', args);
  let count = args.length;
  let opSize = SIZEOF_C + count * 2;
  ASSERT(ml_getOpSizeSlow(ml, offset) >= opSize, 'the c2 should fit the existing space entirely');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, count);
  for (let i = 0; i < count; ++i) {
    ml_enc16(ml, offset + SIZEOF_C + i * 2, args[i]);
  }

  if (opSize < oldSizeof) ml_compileJumpSafe(ml, offset + opSize, oldSizeof - opSize);
  ASSERT(ml_validateSkeleton(ml, 'ml_any2c'));
}

function ml_any2cr(ml, offset, oldSizeof, opCode, args, indexR) {
  TRACE(' -| ml_any2cr | from', offset, 'was len=', oldSizeof, 'to op', ml__opName(opCode), 'with args', args, ', indexR=', indexR, ', new size should be', SIZEOF_C + args.length * 2 + 2);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof oldSizeof === 'number' && offset > 0 && offset < ml.length, 'valid oldSizeof', oldSizeof);
  ASSERT(args instanceof Array, 'args is list of indexes', args);
  ASSERT(typeof indexR === 'number', 'valid indexR', indexR);
  let count = args.length;
  let opSize = SIZEOF_C + count * 2 + 2;
  ASSERT(ml_getOpSizeSlow(ml, offset) >= opSize, 'the cr should fit the existing space entirely');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, count);
  for (let i = 0; i < count; ++i) {
    ml_enc16(ml, offset + SIZEOF_C + i * 2, args[i]);
  }
  ml_enc16(ml, offset + SIZEOF_C + count * 2, indexR);

  ASSERT(opSize <= oldSizeof, 'should fit!');
  if (opSize < oldSizeof) ml_compileJumpSafe(ml, offset + opSize, oldSizeof - opSize);
  ASSERT(ml_validateSkeleton(ml, 'ml_any2cr'));
}

function ml_cr2vv(ml, offset, argCount, opCode, indexA, indexB) {
  TRACE(' -| ml_cr2vv | from', offset, ', argCount=', argCount, 'to op', ml__opName(opCode), 'with args:', indexA, indexB);
  ASSERT(argCount >= 1, 'if this is called for count ops with 0 args then we have a problem... a vv wont fit that');
  // "count with result"
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) >= SIZEOF_VV, 'the vv should fit the existing space entirely');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, indexA);
  ml_enc16(ml, offset + 3, indexB);

  let oldLen = SIZEOF_C + argCount * 2 + 2;
  if (SIZEOF_VV < oldLen) ml_compileJumpSafe(ml, offset + SIZEOF_VV, oldLen - SIZEOF_VV);
  ASSERT(ml_validateSkeleton(ml, 'ml_cr2vv'));
}

function ml_cr2vvv(ml, offset, argCount, opCode, indexA, indexB, indexC) {
  TRACE(' -| ml_cr2vvv | from', offset, ', argCount=', argCount, 'to op', ml__opName(opCode), 'with args:', indexA, indexB, indexC);
  ASSERT(argCount >= 2, 'if this is called for count ops with 1 or 0 args then we have a problem... a vvv wont fit that');
  // "count with result"
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(typeof indexC === 'number' && indexC >= 0, 'valid indexC', indexC);
  ASSERT(ml_getOpSizeSlow(ml, offset) >= SIZEOF_VVV, 'the vvv should fit the existing space entirely');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, indexA);
  ml_enc16(ml, offset + 3, indexB);
  ml_enc16(ml, offset + 5, indexC);

  let oldLen = SIZEOF_C + argCount * 2 + 2;
  if (SIZEOF_VVV < oldLen) ml_compileJumpSafe(ml, offset + SIZEOF_VVV, oldLen - SIZEOF_VVV);
  ASSERT(ml_validateSkeleton(ml, 'ml_cr2vvv'));
}

function ml_cr2cr2(ml, offset, argCount, opCode, indexA, indexB, indexC) {
  // "count with result and any args to count with result with 2 args"
  TRACE(' -| ml_cr2cr2 | from', offset, ', argCount=', argCount, 'to op', ml__opName(opCode), 'with args:', indexA, indexB, indexC);
  ASSERT(argCount >= 2, 'if this is called for count ops with 1 or 0 args then we have a problem... a cr[' + argCount + '] wont fit that');
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(typeof indexC === 'number' && indexC >= 0, 'valid indexC', indexC);
  ASSERT(ml_getOpSizeSlow(ml, offset) >= SIZEOF_CR_2, 'the cr2 should fit the existing space entirely');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, 2); // arg count
  ml_enc16(ml, offset + OFFSET_C_A, indexA);
  ml_enc16(ml, offset + OFFSET_C_B, indexB);
  ml_enc16(ml, offset + OFFSET_C_C, indexC);

  let oldLen = SIZEOF_C + argCount * 2 + 2;
  if (SIZEOF_CR_2 < oldLen) ml_compileJumpSafe(ml, offset + SIZEOF_CR_2, oldLen - SIZEOF_CR_2);
  ASSERT(ml_validateSkeleton(ml, 'ml_cr2cr2'));
}

function ml_cr2c2(ml, offset, argCount, opCode, indexA, indexB) {
  // "count with result"
  let oldArgCount = ml_dec16(ml, offset + 1);
  TRACE(' -| ml_cr2c2 | from', offset, ', with argCount=', oldArgCount, ' and a result var, to a argCount=', argCount, ' without result, op', ml__opName(opCode), ', args:', indexA, indexB);
  // count with result and any args to count with result and (exactly) 2 args
  ASSERT(argCount >= 1, 'if this is called for count ops with 0 args then we have a problem... a c[' + argCount + '] wont fit that');
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) >= SIZEOF_C_2, 'the c2 should fit the existing space entirely');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, 2); // arg count
  ml_enc16(ml, offset + OFFSET_C_A, indexA);
  ml_enc16(ml, offset + OFFSET_C_B, indexB);

  let oldLen = SIZEOF_C + oldArgCount * 2 + 2;
  if (SIZEOF_C_2 < oldLen) ml_compileJumpSafe(ml, offset + SIZEOF_C_2, oldLen - SIZEOF_C_2);
  ASSERT(ml_validateSkeleton(ml, 'ml_cr2c2'));
}

function ml_cr2c(ml, offset, oldArgCount, opCode, args) {
  // "count with result to count"
  // count with result and any args to count without result and any args
  // not "any" because the number of new args can at most be only be one more than the old arg count
  TRACE(' -| ml_cr2c | from', offset, ', with oldArgCount=', oldArgCount, ' and a result var, to a oldArgCount=', oldArgCount, ' without result, op', ml__opName(opCode), ', args:', args);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof oldArgCount === 'number', 'valid oldArgCount', oldArgCount);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(args instanceof Array && args.every(v => typeof v === 'number' && v >= 0));
  ASSERT(oldArgCount + 1 >= args.length, 'cr can holds one index more than c so we can compile one more arg here', oldArgCount, '->', args.length);

  let newArgCount = args.length;
  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, newArgCount);
  for (let i = 0; i < newArgCount; ++i) {
    ml_enc16(ml, offset + SIZEOF_C + i * 2, args[i]);
  }

  let oldLen = SIZEOF_C + oldArgCount * 2 + 2;
  let newLen = SIZEOF_C + newArgCount * 2;
  if (newLen < oldLen) ml_compileJumpSafe(ml, offset + newLen, oldLen - newLen);
  ASSERT(ml_validateSkeleton(ml, 'ml_cr2c'));
}

function ml_vv2vv(ml, offset, opCode, indexA, indexB) {
  TRACE(' -| ml_vv2vv | from', offset, 'to op', ml__opName(opCode), ', index AB:', indexA, indexB);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) === SIZEOF_VV, 'the existing space should be a vv');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, indexA);
  ml_enc16(ml, offset + 3, indexB);

  ASSERT(ml_validateSkeleton(ml, 'ml_vv2vv'));
}

function ml_vvv2vv(ml, offset, opCode, indexA, indexB) {
  TRACE(' -| ml_vvv2vv |', 'to op', ml__opName(opCode), ', args:', indexA, indexB);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) === SIZEOF_VVV, 'the existing space should be a vvv');
  ASSERT(ml_getOpSizeSlow(ml, offset) > SIZEOF_VVV, 'the existing vvv should be larger than a vv');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, indexA);
  ml_enc16(ml, offset + 3, indexB);
  ml_compileJumpSafe(ml, offset + SIZEOF_VV, SIZEOF_VVV - SIZEOF_VV);

  ASSERT(ml_validateSkeleton(ml, 'ml_vvv2vv'));
}

function ml_vvv2c2(ml, offset, opCode, indexA, indexB) {
  TRACE(' -| ml_vvv2c2 |', 'to op', ml__opName(opCode), ', args:', indexA, indexB);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) === SIZEOF_C_2, 'the existing space should be a vvv and that should be a c2');
  ASSERT(SIZEOF_VVV === SIZEOF_C_2, 'need to check here if this changes');

  // note: size(vvv) is same as size(c2)
  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, 2);
  ml_enc16(ml, offset + OFFSET_C_A, indexA);
  ml_enc16(ml, offset + OFFSET_C_B, indexB);

  ASSERT(ml_validateSkeleton(ml, 'ml_vvv2c2'));
}

function ml_vvv2vvv(ml, offset, opCode, indexA, indexB, indexR) {
  TRACE(' -| cr_vvv2vvv |', 'to op', ml__opName(opCode), ', args:', indexA, indexB, indexR);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(typeof indexR === 'number' && indexR >= 0, 'valid indexR', indexR);
  ASSERT(ml_getOpSizeSlow(ml, offset) === SIZEOF_VVV, 'the existing space should be a vvv');

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, indexA);
  ml_enc16(ml, offset + 3, indexB);
  ml_enc16(ml, offset + 5, indexR);

  ASSERT(ml_validateSkeleton(ml, 'ml_vvv2vvv'));
}

function ml_walk(ml, offset, callback) {
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < ml.length, 'offset should be valid and not oob');
  ASSERT(typeof callback === 'function', 'callback should be callable');

  let len = ml.length;
  let op = ml[offset];
  while (offset < len) {
    op = ml[offset];
    ASSERT(!(offset === 0 || op !== ML_START) ? ml_throw(ml, offset, 'should not see op=0 unless offset=0') : 1);
    let sizeof = ml_sizeof(ml, offset, op);
    ASSERT(sizeof > 0, 'ops should occupy space');
    let r = callback(ml, offset, op, sizeof);
    if (r !== undefined) return r;
    offset += sizeof;
  }
}

/**
 * Walk the ml with a callback for each var encountered
 *
 * @param {Uint8Array} ml
 * @param {number} offset
 * @param {Function} callback Called as opCallback(ml, opoffset, optype, opcode, ...args) the actual `args` depend on the optype
 */
function ml_stream(ml, offset, callback) {
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < ml.length, 'offset should be valid and not oob');
  ASSERT(typeof callback === 'function', 'callback should be callable');

  let r;
  let len = ml.length;
  let op = ml[offset];
  while (offset < len) {
    op = ml[offset];
    ASSERT(offset === 0 || op !== ML_START, 'should not see op=0 unless offset=0', 'offset=', offset, 'ml=', ml);

    let sizeof = 0;
    switch (op) {
      case ML_IMP:
      case ML_LT:
      case ML_LTE:
      case ML_NIMP:
      case ML_XOR:
        r = callback(ml, offset, ML_C_2, op, ml_dec16(ml, offset + OFFSET_C_A), ml_dec16(ml, offset + OFFSET_C_B));
        sizeof = SIZEOF_C_2;
        break;

      case ML_ISLT:
      case ML_ISLTE:
      case ML_MINUS:
      case ML_DIV:
        r = callback(ml, offset, ML_VVV, op, ml_dec16(ml, offset + 1), ml_dec16(ml, offset + 3), ml_dec16(ml, offset + 5));
        sizeof = SIZEOF_CR_2;
        break;

      case ML_ALL:
      case ML_DIFF:
      case ML_NALL:
      case ML_NONE:
      case ML_SAME:
      case ML_SOME:
      case ML_XNOR:
        r = callback(ml, offset, ML_C, op, ml_dec16(ml, offset + 1));
        sizeof = SIZEOF_C + ml_dec16(ml, offset + 1) * 2;
        break;

      case ML_ISALL:
      case ML_ISDIFF:
      case ML_ISNALL:
      case ML_ISNONE:
      case ML_ISSAME:
      case ML_ISSOME:
      case ML_PRODUCT:
      case ML_SUM:
        r = callback(ml, offset, ML_CR, op, ml_dec16(ml, offset + 1), ml_dec16(ml, offset + SIZEOF_C + ml_dec16(ml, offset + 1) * 2));
        sizeof = SIZEOF_C + ml_dec16(ml, offset + 1) * 2 + 2;
        break;

      case ML_NOBOOL:
      case ML_NOLEAF:
        r = callback(ml, offset, ML_V, op, ml_dec16(ml, offset + 1));
        sizeof = SIZEOF_V;
        break;

      case ML_JMP:
        r = callback(ml, offset, ML_V, op, ml_dec16(ml, offset + 1));
        sizeof = SIZEOF_V + ml_dec16(ml, offset + 1);
        break;
      case ML_JMP32:
        r = callback(ml, offset, ML_W, op, ml_dec32(ml, offset + 1));
        sizeof = SIZEOF_W + ml_dec32(ml, offset + 1);
        break;

      case ML_NOOP2:
        r = callback(ml, offset, ML_NO_ARGS, op);
        sizeof = 2;
        break;
      case ML_NOOP3:
        r = callback(ml, offset, ML_NO_ARGS, op);
        sizeof = 3;
        break;
      case ML_NOOP4:
        r = callback(ml, offset, ML_NO_ARGS, op);
        sizeof = 4;
        break;

      case ML_NOOP:
      case ML_START:
      case ML_STOP:
        r = callback(ml, offset, ML_NO_ARGS, op);
        sizeof = 1;
        break;

      default:
        TRACE('(ml_walkVars) unknown op: ' + ml[offset], ' at', offset);
        ml_throw(ml, offset, '(ml_walkVars) unknown op');
    }

    ASSERT(sizeof > 0, 'ops should occupy space');
    if (r !== undefined) return r;
    offset += sizeof;
  }
}

function ml_validateSkeleton(ml, msg) {
  TRACE_SILENT('--- ml_validateSkeleton', msg);
  let started = false;
  let stopped = false;
  ml_walk(ml, 0, (ml, offset, op) => {
    if (op === ML_START && offset === 0) started = true;
    if (op === ML_START && offset !== 0) ml_throw(ml, offset, 'ml_validateSkeleton: Found ML_START at offset', offset);
    if (op === ML_STOP) stopped = true;
    else if (stopped) ml_throw(ml, offset, 'ml_validateSkeleton: Should stop after encountering a stop but did not');
  });

  if (!started || !stopped) ml_throw(ml, ml.length, 'ml_validateSkeleton: Missing a ML_START or ML_STOP');
  TRACE_SILENT('--- PASS ml_validateSkeleton');
  return true;
}

function ml_getRecycleOffset(ml, fromOffset, requiredSize) {
  TRACE(' - ml_getRecycleOffset looking for at least', requiredSize, 'bytes of free space');
  ASSERT(typeof fromOffset === 'number' && fromOffset >= 0, 'expecting fromOffset', fromOffset);
  ASSERT(typeof requiredSize === 'number' && requiredSize > 0, 'expecting size', requiredSize);
  // find a jump which covers at least the requiredSize
  return ml_walk(ml, fromOffset, (ml, offset, op) => {
    TRACE('   - considering op', op, 'at', offset);
    if (op === ML_JMP || op === ML_JMP32) {
      let size = ml_getOpSizeSlow(ml, offset);
      TRACE('   - found jump of', size, 'bytes at', offset + ', wanted', requiredSize, (requiredSize <= size ? ' so is ok!' : ' so is too small'));
      if (size >= requiredSize) return offset;
    }
  });
}

function ml_getRecycleOffsets(ml, fromOffset, slotCount, sizePerSlot) {
  TRACE(' - ml_getRecycleOffsets looking for empty spaces to fill', slotCount, 'times', sizePerSlot, 'bytes');
  ASSERT(typeof fromOffset === 'number' && fromOffset >= 0, 'expecting fromOffset', fromOffset);
  ASSERT(typeof slotCount === 'number' && slotCount > 0, 'expecting slotCount', slotCount);
  ASSERT(typeof sizePerSlot === 'number' && sizePerSlot > 0, 'expecting sizePerSlot', sizePerSlot);

  let spaces = [];

  // find a jump which covers at least the requiredSize
  ml_walk(ml, fromOffset, (ml, offset, op) => {
    TRACE('   - considering op', op, 'at', offset);
    if (op === ML_JMP || op === ML_JMP32) {
      let size = ml_getOpSizeSlow(ml, offset);
      TRACE('   - found jump of', size, 'bytes at', offset + ', wanted', sizePerSlot, (sizePerSlot <= size ? ' so is ok!' : ' so is too small'));
      if (size >= sizePerSlot) {
        spaces.push(offset); // only add it once!
        do { // remove as many from count as there fit in this empty space
          --slotCount;
          size -= sizePerSlot;
        } while (slotCount && size >= sizePerSlot);
        if (!slotCount) return true;
      }
    }
  });

  if (slotCount) return false; // unable to collect enough spaces
  return spaces;
}

function ml_recycles(ml, bins, loops, sizeofOp, callback) {
  let i = 0;
  while (i < loops) {
    let currentRecycleOffset = bins.pop();
    ASSERT(ml_dec8(ml, currentRecycleOffset) === ML_JMP, 'should only get jumps here'); // might trap a case where we clobber
    let sizeLeft = ml_getOpSizeSlow(ml, currentRecycleOffset);
    ASSERT(sizeLeft >= sizeofOp, 'this is what should have been asked for when getting recycled spaces');
    do {
      let stop = callback(currentRecycleOffset, i, sizeLeft);
      if (stop) return;
      ++i;
      sizeLeft -= sizeofOp;
      currentRecycleOffset += sizeofOp;
    } while (sizeLeft >= sizeofOp && i < loops);
    if (sizeLeft) ml_compileJumpSafe(ml, currentRecycleOffset, sizeLeft);
    ASSERT(ml_validateSkeleton(ml), 'ml_recycles'); // cant check earlier
  }
}

function ml_getOpSizeSlow(ml, offset) {
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < ml.length, 'ml_getOpSizeSlow OOB');
  // this is much slower compared to using the constants because it has to read from the ML
  // this function exists to suplement recycling, where you must read the size of the jump
  // otherwise you won't know how much space is left after recycling
  let size = ml_sizeof(ml, offset, ml[offset]);
  TRACE_SILENT(' - ml_getOpSizeSlow', offset, ml.length, '-->', size);
  return size;
}

function ml_recycleC3(ml, offset, op, indexA, indexB, indexC) {
  // explicitly rewrite a count with len=3
  let jumpOp = ml_dec8(ml, offset);
  TRACE('- ml_recycleC3 | offset=', offset, ', op=', op, indexA, indexB, indexC, jumpOp);
  ASSERT(jumpOp === ML_JMP || jumpOp === ML_JMP32, 'expecting to recycle a space that starts with a jump');
  ASSERT((jumpOp === ML_JMP ? SIZEOF_V + ml_dec16(ml, offset + 1) : SIZEOF_W + ml_dec32(ml, offset + 1)) >= SIZEOF_C + 6, 'a c3 should fit'); // op + len + 3*2

  let currentSize = (jumpOp === ML_JMP ? SIZEOF_V + ml_dec16(ml, offset + 1) : SIZEOF_W + ml_dec32(ml, offset + 1));
  let newSize = SIZEOF_C + 6;
  let remainsEmpty = currentSize - newSize;
  if (remainsEmpty < 0) THROW('recycled OOB');
  TRACE('- putting a c3', op, 'at', offset, ', old size=', currentSize, ', new size=', newSize, ', leaving', remainsEmpty, 'for a jump');

  ml_enc8(ml, offset, op);
  ml_enc16(ml, offset + 1, 3);
  ml_enc16(ml, offset + 3, indexA);
  ml_enc16(ml, offset + 5, indexB);
  ml_enc16(ml, offset + 7, indexC);

  if (remainsEmpty) ml_compileJumpSafe(ml, offset + newSize, remainsEmpty);
}

function ml_recycleVV(ml, offset, op, indexA, indexB) {
  let jumpOp = ml_dec8(ml, offset);
  TRACE('- ml_recycleVV', offset, op, indexA, indexB, jumpOp);
  ASSERT(jumpOp === ML_JMP || jumpOp === ML_JMP32, 'expecting to recycle a space that starts with a jump');
  ASSERT((jumpOp === ML_JMP ? SIZEOF_V + ml_dec16(ml, offset + 1) : SIZEOF_W + ml_dec32(ml, offset + 1)) >= SIZEOF_VV, 'a vv should fit'); // op + len + 3*2

  let currentSize = (jumpOp === ML_JMP ? SIZEOF_V + ml_dec16(ml, offset + 1) : SIZEOF_W + ml_dec32(ml, offset + 1));
  let remainsEmpty = currentSize - SIZEOF_VV;
  if (remainsEmpty < 0) THROW('recycled OOB');
  TRACE('- putting a vv', op, 'at', offset, 'of size', currentSize, 'leaving', remainsEmpty, 'for a jump');

  ml_enc8(ml, offset, op);
  ml_enc16(ml, offset + 1, indexA);
  ml_enc16(ml, offset + 3, indexB);

  if (remainsEmpty) ml_compileJumpSafe(ml, offset + SIZEOF_VV, remainsEmpty);
}

function ml__debug(ml, offset, max, problem, mlAlways, _from_ml_throw) {
  let getDomain = problem && problem.getDomain;
  let names = problem && problem.varNames;

  function ml_index(offset) {
    let index = _dec16(ml, offset);
    return '{index=' + index + (problem && index < names.length ? ',name=' + names[index] : '') + (problem ? ',' + domain__debug(getDomain(index)) : '') + '}';
  }

  function ml_16(offset) {
    return _dec16(ml, offset);
  }

  let AB; // grrr switches and let are annoying
  let rv = [];

  if (max < 0) max = ml.length;
  let pc = offset;
  let count = 0;
  while (count++ < max && pc < ml.length) {
    let name = '';
    let op = ml[pc];
    /* eslint-disable no-fallthrough */// should have an option to allow it when explicitly stated like below...
    switch (op) {
      case ML_START:
        if (pc !== 0) {
          TRACE('collected debugs up to error:', rv);
          if (!_from_ml_throw) ml_throw(ml, pc, 'ML_START at non-zero');
          rv.push('unused_error(0)');
          return rv.join('\n');
        }
        break;

      case ML_IMP:
        if (!name) name = '->';
      /* fall-through */
      case ML_NIMP:
        if (!name) name = '!->';
      /* fall-through */
      case ML_LT:
        if (!name) name = '<';
      /* fall-through */
      case ML_LTE:
        if (!name) name = '<=';
      /* fall-through */
      case ML_XOR:
        if (!name) name = '^';
        rv.push(ml_index(pc + OFFSET_C_A) + ' ' + name + ' ' + ml_index(pc + OFFSET_C_B));
        break;

      case ML_ISLT:
        if (!name) name = '<?';
      /* fall-through */
      case ML_ISLTE:
        if (!name) name = '<=?';
        AB = ml_index(pc + 1) + ' ' + name + ' ' + ml_index(pc + 3);
        rv.push(ml_index(pc + 5) + ' = ' + AB);
        break;

      case ML_SUM:
        if (!name) name = 'sum';
      /* fall-through */
      case ML_PRODUCT:
        if (!name) name = 'product';
      /* fall-through */
      case ML_ISALL:
        if (!name) name = 'isall';
      /* fall-through */
      case ML_ISDIFF:
        if (!name) name = 'isdiff';
      /* fall-through */
      case ML_ISNALL:
        if (!name) name = 'isnall';
      /* fall-through */
      case ML_ISSAME:
        if (!name) name = 'issame';
      /* fall-through */
      case ML_ISSOME:
        if (!name) name = 'issome';
      /* fall-through */
      case ML_ISNONE:
        if (!name) name = 'isnone';
        let vars = '';
        let varcount = ml_16(pc + 1);
        for (let i = 0; i < varcount; ++i) {
          vars += ml_index(pc + SIZEOF_C + i * 2) + ' ';
        }
        vars = name + '(' + vars + ')';
        vars = ml_index(pc + SIZEOF_C + varcount * 2) + ' = ' + vars;
        rv.push(vars);
        break;

      case ML_ALL:
        if (!name) name = 'all';
      /* fall-through */
      case ML_NALL:
        if (!name) name = 'nall';
      /* fall-through */
      case ML_SAME:
        if (!name) name = 'same';
      /* fall-through */
      case ML_SOME:
        if (!name) name = 'some';
      /* fall-through */
      case ML_NONE:
        if (!name) name = 'none';
      /* fall-through */
      case ML_XNOR:
        if (!name) name = 'xnor';
      /* fall-through */
      case ML_DIFF:
        if (!name) name = 'diff';
        let xvars = '';
        let xvarcount = ml_16(pc + 1);
        for (let i = 0; i < xvarcount; ++i) {
          xvars += ml_index(pc + SIZEOF_C + i * 2) + ' ';
        }
        xvars = name + '(' + xvars + ')';
        rv.push(xvars);
        break;

      case ML_MINUS:
        if (!name) name = '-';
      /* fall-through */
      case ML_DIV:
        if (!name) name = '/';
        AB = ml_index(pc + 1) + ' ' + name + ' ' + ml_index(pc + 3);
        rv.push(ml_index(pc + 5) + ' = ' + AB);
        break;

      case ML_JMP:
        rv.push('jmp(' + _dec16(ml, pc + 1) + ')');
        break;
      case ML_JMP32:
        rv.push('jmp32(' + _dec32(ml, pc + 1) + ')');
        break;

      case ML_NOBOOL:
        rv.push('nobool(' + _dec16(ml, pc + 1) + ')');
        break;
      case ML_NOLEAF:
        rv.push('noleaf(' + _dec16(ml, pc + 1) + ')');
        break;
      case ML_NOOP:
        rv.push('noop(1)');
        break;
      case ML_NOOP2:
        rv.push('noop(2)');
        break;
      case ML_NOOP3:
        rv.push('noop(3)');
        break;
      case ML_NOOP4:
        rv.push('noop(4)');
        break;
      case ML_STOP:
        rv.push('stop()');
        break;

      default:
        THROW('add me [pc=' + pc + ', op=' + ml[pc] + ']');
    }

    let size = ml_sizeof(ml, pc, op);
    //getTerm().log('size was:', size, 'rv=', rv);
    if (max !== 1 || mlAlways) rv.push('\x1b[90m' + size + 'b (' + pc + ' ~ ' + (pc + size) + ') -> 0x   ' + [...ml.slice(pc, pc + Math.min(size, 100))].map(c => (c < 16 ? '0' : '') + c.toString(16)).join(' ') + (size > 100 ? '... (trunced)' : '') + '\x1b[0m');
    pc += size;
  }

  return max === 1 ? rv.join('\n') : ' ## ML Debug:\n' + rv.join('\n') + '\n ## End of ML Debug' + ((offset || pc < ml.length) ? offset ? ' (did not start at begin of ml!)' : ' (did not list all ops, ml at ' + pc + ' / ' + ml.length + '))...' : '') + '\n';
}
function ml__opName(op) {
  ASSERT(typeof op === 'number', 'op should be a constant number');
  switch (op) {
    case ML_ALL: return 'ML_ALL';
    case ML_START: return 'ML_START';
    case ML_SAME: return 'ML_SAME';
    case ML_LT: return 'ML_LT';
    case ML_LTE: return 'ML_LTE';
    case ML_XOR: return 'ML_XOR';
    case ML_XNOR: return 'ML_XNOR';
    case ML_IMP: return 'ML_IMP';
    case ML_NIMP: return 'ML_NIMP';
    case ML_ISSAME: return 'ML_ISSAME';
    case ML_ISDIFF: return 'ML_ISDIFF';
    case ML_ISLT: return 'ML_ISLT';
    case ML_ISLTE: return 'ML_ISLTE';
    case ML_SUM: return 'ML_SUM';
    case ML_PRODUCT: return 'ML_PRODUCT';
    case ML_ISALL: return 'ML_ISALL';
    case ML_ISNALL: return 'ML_ISNALL';
    case ML_ISSOME: return 'ML_ISSOME';
    case ML_ISNONE: return 'ML_ISNONE';
    case ML_NALL: return 'ML_NALL';
    case ML_SOME: return 'ML_SOME';
    case ML_NONE: return 'ML_NONE';
    case ML_DIFF: return 'ML_DISTINCT';
    case ML_MINUS: return 'ML_MINUS';
    case ML_DIV: return 'ML_DIV';
    case ML_NOBOOL: return 'ML_NOBOOL';
    case ML_NOLEAF: return 'ML_NOLEAF';
    case ML_JMP: return 'ML_JMP';
    case ML_JMP32: return 'ML_JMP32';
    case ML_NOOP: return 'ML_NOOP';
    case ML_NOOP2: return 'ML_NOOP2';
    case ML_NOOP3: return 'ML_NOOP3';
    case ML_NOOP4: return 'ML_NOOP4';
    case ML_STOP: return 'ML_STOP';
    default:
      THROW('[ML] unknown op, fixme [' + op + ']');
  }
}

function ml_throw(ml, offset, msg) {
  let term = getTerm();
  term.error('\nThere was an ML related error;', msg);
  let before = ml.slice(Math.max(0, offset - 30), offset);
  let after = ml.slice(offset, offset + 20);
  term.error('ML at error (offset=' + offset + '/' + ml.length + '):', before, after);
  term.error('->', ml__debug(ml, offset, 1, undefined, true, true));
  THROW(msg);
}

function ml_getOpList(ml) {
  let pc = 0;
  let rv = [];
  while (pc < ml.length) {
    let op = ml[pc];
    switch (op) {
      case ML_START:
        if (pc !== 0) {
          rv.push('error(0)');
          return rv.join(',');
        }
        break;

      case ML_SAME:
        rv.push('same');
        break;
      case ML_LT:
        rv.push('lt');
        break;
      case ML_LTE:
        rv.push('lte');
        break;
      case ML_ALL:
        rv.push('all');
        break;
      case ML_NONE:
        rv.push('none');
        break;
      case ML_XOR:
        rv.push('xor');
        break;
      case ML_XNOR:
        rv.push('xnor');
        break;
      case ML_IMP:
        rv.push('imp');
        break;
      case ML_NIMP:
        rv.push('nimp');
        break;

      case ML_ISLT:
        rv.push('islt');
        break;
      case ML_ISLTE:
        rv.push('islte');
        break;

      case ML_SUM:
        rv.push('sum');
        break;
      case ML_PRODUCT:
        rv.push('product');
        break;

      case ML_ISALL:
        rv.push('isall');
        break;
      case ML_ISDIFF:
        rv.push('isdiff');
        break;
      case ML_ISNALL:
        rv.push('isnall');
        break;
      case ML_ISNONE:
        rv.push('isnone');
        break;
      case ML_ISSAME:
        rv.push('issame');
        break;
      case ML_ISSOME:
        rv.push('issome');
        break;

      case ML_NALL:
        rv.push('nall');
        break;
      case ML_SOME:
        rv.push('some');
        break;
      case ML_DIFF:
        rv.push('diff');
        break;

      case ML_MINUS:
        rv.push('minus');
        break;
      case ML_DIV:
        rv.push('div');
        break;

      case ML_NOBOOL:
      case ML_NOLEAF:
      case ML_JMP:
      case ML_JMP32:
      case ML_NOOP:
      case ML_NOOP2:
      case ML_NOOP3:
      case ML_NOOP4:
      case ML_STOP:
        break;

      default:
        rv.push('??!??');
    }

    pc += ml_sizeof(ml, pc, op);
  }

  return rv.sort((a, b) => a < b ? -1 : 1).join(',');
}

function ml_heapSort16bitInline(ml, offset, argCount) {
  _ml_heapSort16bitInline(ml, offset, argCount);
  //TRACE('     - op now:', ml__debug(ml, offset-SIZEOF_C, 1))
  TRACE('     ### </ml_heapSort16bitInline> values after:', new Array(argCount).fill(0).map((_, i) => _dec16(ml, offset + i * 2)).join(' '), 'buf:', ml.slice(offset, offset + argCount * 2).join(' '));
  ASSERT(ml_validateSkeleton(ml, 'ml_heapSort16bitInline'));
}
function _ml_heapSort16bitInline(ml, offset, argCount) {
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && (offset === 0 || (offset > 0 && offset < ml.length)), 'valid offset', ml.length, offset, argCount);
  ASSERT(typeof argCount === 'number' && (argCount === 0 || (argCount > 0 && offset + argCount * 2 <= ml.length)), 'valid count', ml.length, offset, argCount);

  TRACE('     ### <ml_heapSort16bitInline>, argCount=', argCount, ', offset=', offset, ', buf=', ml.slice(offset, offset + argCount * 2));
  TRACE('     - values before:', new Array(argCount).fill(0).map((_, i) => _dec16(ml, offset + i * 2)).join(' '));

  if (argCount <= 1) {
    TRACE(' - (argCount <= 1 so finished)');
    return;
  }

  ml_heapify(ml, offset, argCount);

  let end = argCount - 1;
  while (end > 0) {
    TRACE('     - swapping first elemement (should be biggest of values left to do) [', _dec16(ml, offset), '] with last [', _dec16(ml, offset + end * 2), '] and reducing end [', end, '->', end - 1, ']');
    ml_swap16(ml, offset, offset + end * 2);
    TRACE('     - (total) buffer now: Uint8Array(', [].map.call(ml.slice(offset, offset + argCount * 2), b => (b < 16 ? '0' : '') + b.toString(16)).join(' '), ')');
    --end;
    ml_heapRepair(ml, offset, 0, end);
  }
}
function ml_heapParent(index) {
  return Math.floor((index - 1) / 2);
}
function ml_heapLeft(index) {
  return index * 2 + 1;
}
function ml_heapRight(index) {
  return index * 2 + 2;
}
function ml_heapify(ml, offset, len) {
  TRACE('     - ml_heapify', ml.slice(offset, offset + len * 2), offset, len);

  let start = ml_heapParent(len - 1);
  while (start >= 0) {
    ml_heapRepair(ml, offset, start, len - 1);
    --start; // wont this cause it to do it redundantly twice?
  }

  TRACE('     - ml_heapify end');
}
function ml_heapRepair(ml, offset, startIndex, endIndex) {
  TRACE('     - ml_heapRepair', offset, startIndex, endIndex, 'Uint8Array(', [].map.call(ml.slice(offset + startIndex * 2, offset + startIndex * 2 + (endIndex - startIndex + 1) * 2), b => (b < 16 ? '0' : '') + b.toString(16)).join(' '), ')');
  let parentIndex = startIndex;
  let parentValue = ml_dec16(ml, offset + parentIndex * 2);
  let leftIndex = ml_heapLeft(parentIndex);
  TRACE('     -- first leftIndex=', leftIndex, 'end=', endIndex);

  while (leftIndex <= endIndex) {
    TRACE('       - sift loop. indexes; parent=', parentIndex, 'left=', leftIndex, 'right=', ml_heapRight(parentIndex), 'values; parent=', _dec16(ml, offset + parentIndex * 2) + '/' + parentValue, ' left=', _dec16(ml, offset + leftIndex * 2), ' right=', ml_heapRight(parentIndex) <= endIndex ? _dec16(ml, offset + ml_heapRight(parentIndex) * 2) : 'void');
    let leftValue = ml_dec16(ml, offset + leftIndex * 2);
    let swapIndex = parentIndex;
    let swapValue = parentValue;

    TRACE('         - swap<left?', swapValue, leftValue, swapValue < leftValue ? 'yes' : 'no');
    if (swapValue < leftValue) {
      swapIndex = leftIndex;
      swapValue = leftValue;
    }

    let rightIndex = ml_heapRight(parentIndex);
    TRACE('         - right index', rightIndex, '<=', endIndex, rightIndex <= endIndex ? 'yes it has a right child' : 'no right child');
    if (rightIndex <= endIndex) {
      let rightValue = ml_dec16(ml, offset + rightIndex * 2);
      TRACE('         - swap<right?', swapValue, rightValue);
      if (swapValue < rightValue) {
        swapIndex = rightIndex;
        swapValue = rightValue;
      }
    }

    TRACE('           - result; parent=', parentIndex, 'swap=', swapIndex, ', values; parent=', parentValue, ', swap=', swapValue, '->', (swapIndex === parentIndex ? 'finished, parent=swap' : 'should swap'));

    if (swapIndex === parentIndex) {
      TRACE('     - ml_heapRepair end early:', 'Uint8Array(', [].map.call(ml.slice(offset + startIndex * 2, offset + startIndex * 2 + (endIndex - startIndex + 1) * 2), b => (b < 16 ? '0' : '') + b.toString(16)).join(' '), ')');
      return;
    }
    // "swap"
    ml_enc16(ml, offset + parentIndex * 2, swapValue);
    ml_enc16(ml, offset + swapIndex * 2, parentValue);
    TRACE('             - setting parent to index=', swapIndex, ', value=', swapValue);
    parentIndex = swapIndex;
    // note: parentValue remains the same because the swapped child becomes the new parent and it gets the old parent value

    leftIndex = ml_heapLeft(parentIndex);
    TRACE('           - next left:', leftIndex, 'end:', endIndex);
  }

  TRACE('     - ml_heapRepair end:', ml.slice(offset + startIndex * 2, offset + startIndex * 2 + (endIndex - startIndex + 1) * 2).join(' '));
}
function ml_swap16(ml, indexA, indexB) {
  let A = ml_dec16(ml, indexA);
  let B = ml_dec16(ml, indexB);
  ml_enc16(ml, indexA, B);
  ml_enc16(ml, indexB, A);
}

// BODY_STOP

export {
  ML_ALL,
  ML_NOBOOL,
  ML_NOLEAF,
  ML_DIFF,
  ML_DIV,
  ML_IMP,
  ML_ISALL,
  ML_ISLT,
  ML_ISLTE,
  ML_ISNALL,
  ML_ISNONE,
  ML_ISDIFF,
  ML_ISSAME,
  ML_ISSOME,
  ML_JMP,
  ML_JMP32,
  ML_LT,
  ML_LTE,
  ML_MINUS,
  ML_NALL,
  ML_NIMP,
  ML_NONE,
  ML_NOOP,
  ML_NOOP2,
  ML_NOOP3,
  ML_NOOP4,
  ML_PRODUCT,
  ML_SAME,
  ML_SOME,
  ML_START,
  ML_STOP,
  ML_SUM,
  ML_XNOR,
  ML_XOR,

  SIZEOF_V,
  SIZEOF_W,
  SIZEOF_VV,
  SIZEOF_VVV,
  SIZEOF_C,
  SIZEOF_C_2,
  SIZEOF_CR_2,

  OFFSET_C_A,
  OFFSET_C_B,
  OFFSET_C_C,
  OFFSET_C_R,

  ML_NO_ARGS,
  ML_V,
  ML_W,
  ML_VV,
  ML_VVV,
  ML_C,
  ML_CR,
  ML_C8R,

  ml__debug,
  ml__opName,
  ml_getOpList,
  ml_countConstraints,
  ml_dec8,
  ml_dec16,
  ml_dec32,
  ml_enc8,
  ml_enc16,
  ml_enc32,
  ml_eliminate,
  ml_getRecycleOffset,
  ml_getRecycleOffsets,
  ml_getOpSizeSlow,
  ml_hasConstraint,
  ml_heapSort16bitInline,
  _ml_heapSort16bitInline,
  ml_compileJumpSafe,
  ml_compileJumpAndConsolidate,
  ml_pump,
  ml_recycles,
  ml_recycleC3,
  ml_recycleVV,
  ml_sizeof,
  ml_stream,
  ml_throw,
  ml_validateSkeleton,
  ml_walk,

  ml_any2c,
  ml_any2cr,
  ml_c2vv,
  ml_cx2cx,
  ml_c2c2,
  ml_cr2c,
  ml_cr2c2,
  ml_cr2cr2,
  ml_cr2vv,
  ml_cr2vvv,
  ml_vv2vv,
  ml_vvv2c2,
  ml_vvv2vv,
  ml_vvv2vvv,
};
