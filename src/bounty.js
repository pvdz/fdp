import {
  ASSERT,
  ASSERT_NORDOM,
  getTerm,
  TRACE,
  THROW,
} from '../../fdlib/src/helpers';
import {
  domain__debug,
  domain_getValue,
} from '../../fdlib/src/domain';

import {
  ML_ALL,
  ML_NOBOOL,
  ML_NOLEAF,
  ML_DIFF,
  ML_DIV,
  ML_IMP,
  ML_ISALL,
  ML_ISDIFF,
  ML_ISLT,
  ML_ISLTE,
  ML_ISNALL,
  ML_ISNONE,
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

  OFFSET_C_A,
  OFFSET_C_B,

  SIZEOF_V,
  SIZEOF_W,
  SIZEOF_VVV,
  SIZEOF_C,
  SIZEOF_C_2,

  ml__debug,
  ml_dec16,
  ml_dec32,
  ml_throw,
} from './ml';

// BODY_START

let bounty_flagCounter = 0;
const BOUNTY_NO_FLAGS = bounty_flagCounter;
const BOUNTY_FLAG_NOT_BOOLY = ++bounty_flagCounter; // booly = when only used in bool ops (like nall) or as the lhs of a reifier
const BOUNTY_FLAG_OTHER = ++bounty_flagCounter;

const BOUNTY_FLAG_DIFF = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_IMP_LHS = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_IMP_RHS = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_ISALL_ARG = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_ISALL_RESULT = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_ISLTE_ARG = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_ISSAME_ARG = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_ISSAME_RESULT = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_ISSOME_RESULT = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_LTE_LHS = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_LTE_RHS = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_NALL = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_SOME = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_SUM_RESULT = 1 << ++bounty_flagCounter;
const BOUNTY_FLAG_XOR = 1 << ++bounty_flagCounter;
const BOUNTY_JUST_IGNORE = 1 << ++bounty_flagCounter;

ASSERT(bounty_flagCounter <= 32, 'can only run with 16 flags, or must increase flag size');

const BOUNTY_LINK_COUNT = 1; // should it simply trunc over 255?
const BOUNTY_META_FLAGS = 32; // steps of 8 (bits per byte)
const BOUNTY_MAX_OFFSETS_TO_TRACK = 20; // perf case bounty size when this is: 5->1mb, 20->3mb
const BOUNTY_BYTES_PER_OFFSET = 4;

const BOUNTY_SIZEOF_HEADER = BOUNTY_LINK_COUNT + (BOUNTY_META_FLAGS / 2);
const BOUNTY_SIZEOF_OFFSETS = BOUNTY_MAX_OFFSETS_TO_TRACK * BOUNTY_BYTES_PER_OFFSET; // need to store 32bit per offset (more like 24 but whatever)
const BOUNTY_SIZEOF_VAR = BOUNTY_SIZEOF_HEADER + BOUNTY_SIZEOF_OFFSETS;

/**
 * @param {Uint8Array} ml
 * @param {Object} problem
 * @param {Uint8Array} [bounty]
 */
function bounty_collect(ml, problem, bounty) {
  TRACE('\n ## bounty_collect', ml.length < 50 ? ml.join(' ') : '');

  let varNames = problem.varNames;
  let varCount = varNames.length;
  let getAlias = problem.getAlias;
  let getDomain = problem.getDomain;

  let pc = 0;

  if (!bounty) {
    bounty = new Uint8Array(varCount * BOUNTY_SIZEOF_VAR);
    TRACE('Created bounty buffer. Size:', bounty.length);
  }
  bounty.fill(0); // even for new buffer because they are not guaranteed to be zero filled (most like not)
  ASSERT(bounty instanceof Uint8Array);

  bountyLoop();

  // note: do not auto-mark booly-pairs as BOOLY here! (for example `x^y,x!=z` could break if x!=y)

  TRACE(` - There are ${getDeadCount(bounty)} dead vars, ${getLeafCount(bounty)} leaf vars, full distribution: ${getOccurrenceCount(bounty)} other vars`);

  return bounty;

  function getBountyOffset(varIndex) {
    return varIndex * BOUNTY_SIZEOF_VAR;
  }

  function getOffsetsOffset(varIndex) {
    return varIndex * BOUNTY_SIZEOF_VAR + BOUNTY_SIZEOF_HEADER;
  }

  function collect(delta, metaFlags) {
    TRACE('   ! collect(', delta, ',', _bounty__debugMeta(metaFlags), ')');
    ASSERT(typeof delta === 'number' && delta > 0, 'delta should be >0 number', delta);
    ASSERT(pc + delta > 0 && pc + delta < ml.length, 'offset should be within bounds of ML');
    ASSERT(typeof metaFlags === 'number' && metaFlags > 0, 'at least one metaFlags should be passed on', metaFlags, metaFlags.toString(2));

    let index = ml_dec16(ml, pc + delta);
    ASSERT(typeof index === 'number', 'fetched index should be number');
    ASSERT(!isNaN(index) && index >= 0 && index <= 0xffff, 'should be a valid index', index);
    index = getAlias(index);
    ASSERT(typeof index === 'number', 'fetched alias should be number');
    ASSERT(!isNaN(index) && index >= 0 && index <= 0xffff, 'should be a valid index', index);

    let domain = getDomain(index, true);
    TRACE('     - index=', index, 'domain=', domain__debug(domain));
    ASSERT_NORDOM(domain);
    if (domain_getValue(domain) >= 0) {
      TRACE('      - ignore all constants. solved vars and constants are not relevant to bounty');
      return;
    }

    let varOffset = getBountyOffset(index);

    //ASSERT(bounty[varOffset] < 0xff, 'constraint count should not overflow');

    let countIndex = bounty[varOffset]++; // count, but as zero-offset

    let flagsOffset = varOffset + BOUNTY_LINK_COUNT;
    if (countIndex >= 0xff) {
      // hardcoded limit. just ignore this var. we cant safely optimize this.
      ASSERT(BOUNTY_META_FLAGS === 32, 'update code if this changes');
      _enc32(bounty, flagsOffset, BOUNTY_JUST_IGNORE);
    } else {
      ASSERT(BOUNTY_META_FLAGS === 32, 'update code if this changes because they currently only write 16bits');
      let currentFlags = _dec32(bounty, flagsOffset);

      TRACE('     >> collecting for index=', index, ' -> count now:', bounty[varOffset], 'flags:', _bounty__debugMeta(currentFlags), '|=', _bounty__debugMeta(metaFlags), ' -> ', _bounty__debugMeta(currentFlags | metaFlags), 'from', flagsOffset, 'domain:', domain__debug(domain));

      if (countIndex < BOUNTY_MAX_OFFSETS_TO_TRACK) {
        let offsetsOffset = getOffsetsOffset(index);
        let nextOffset = offsetsOffset + countIndex * BOUNTY_BYTES_PER_OFFSET;
        TRACE('       - tracking offset; countIndex=', countIndex, ', putting offset at', nextOffset);
        _enc32(bounty, nextOffset, pc);
      } else {
        TRACE('       - unable to track offset; countIndex beyond max;', countIndex, '>', BOUNTY_MAX_OFFSETS_TO_TRACK);
      }

      ASSERT(BOUNTY_META_FLAGS === 32, 'update code if this changes');
      _enc32(bounty, flagsOffset, currentFlags | metaFlags);
    }
  }

  function bountyLoop() {
    pc = 0;
    TRACE(' - bountyLoop');
    while (pc < ml.length) {
      let pcStart = pc;
      let op = ml[pc];
      TRACE(' -- CT pc=' + pc + ', op: ' + ml__debug(ml, pc, 1, problem));
      switch (op) {
        case ML_LT:
          // lt always has 2 args (any other wouldnt make sense) but is still a c-args op
          collect(OFFSET_C_A, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(OFFSET_C_B, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          pc += SIZEOF_C_2;
          break;

        case ML_LTE:
          // lte always has 2 args (any other wouldnt make sense) but is still a c-args op
          collect(OFFSET_C_A, BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_NOT_BOOLY);
          collect(OFFSET_C_B, BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_NOT_BOOLY);
          pc += SIZEOF_C_2;
          break;

        case ML_XOR: {
          // xor always has 2 args (any other wouldnt make sense) but is still a c-args op
          collect(OFFSET_C_A, BOUNTY_FLAG_XOR);
          collect(OFFSET_C_B, BOUNTY_FLAG_XOR);
          pc += SIZEOF_C_2;
          break;
        }

        case ML_XNOR: {
          let nlen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < nlen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER);
          }
          pc += SIZEOF_C + nlen * 2;
          break;
        }

        case ML_IMP:
          collect(OFFSET_C_A, BOUNTY_FLAG_IMP_LHS);
          collect(OFFSET_C_B, BOUNTY_FLAG_IMP_RHS);
          pc += SIZEOF_C_2;
          break;

        case ML_NIMP:
          collect(OFFSET_C_A, BOUNTY_FLAG_OTHER);
          collect(OFFSET_C_B, BOUNTY_FLAG_OTHER);
          pc += SIZEOF_C_2;
          break;

        case ML_ALL: {
          let nlen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < nlen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER);
          }
          pc += SIZEOF_C + nlen * 2;
          break;
        }

        case ML_NALL:
          let nlen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < nlen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_NALL);
          }
          pc += SIZEOF_C + nlen * 2;
          break;

        case ML_SAME: {
          // should be aliased but if the problem rejected there may be eqs like this left
          // (bounty is also used for generating the dsl problem)
          let nlen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < nlen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          }
          pc += SIZEOF_C + nlen * 2;
          break;
        }

        case ML_SOME: {
          let nlen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < nlen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_SOME);
          }
          pc += SIZEOF_C + nlen * 2;
          break;
        }

        case ML_NONE: {
          let nlen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < nlen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER);
          }
          pc += SIZEOF_C + nlen * 2;
          break;
        }

        case ML_ISSAME: {
          let nlen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < nlen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_ISSAME_ARG | BOUNTY_FLAG_NOT_BOOLY);
          }
          collect(SIZEOF_C + nlen * 2, BOUNTY_FLAG_ISSAME_RESULT); // R
          pc += SIZEOF_C + nlen * 2 + 2;
          break;
        }

        case ML_ISSOME: {
          let ilen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < ilen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER);
          }
          collect(SIZEOF_C + ilen * 2, BOUNTY_FLAG_ISSOME_RESULT); // R
          pc += SIZEOF_C + ilen * 2 + 2;
          break;
        }

        case ML_DIFF:
          // note: diff "cant" have multiple counts of same var because that would reject
          let dlen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < dlen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_DIFF | BOUNTY_FLAG_NOT_BOOLY);
          }
          pc += SIZEOF_C + dlen * 2;
          break;

        case ML_ISDIFF: {
          let ilen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < ilen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          }
          collect(SIZEOF_C + ilen * 2, BOUNTY_FLAG_OTHER); // R
          pc += SIZEOF_C + ilen * 2 + 2;
          break;
        }

        case ML_ISLT:
          collect(1, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(3, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(5, BOUNTY_FLAG_OTHER);
          pc += SIZEOF_VVV;
          break;

        case ML_ISLTE:
          collect(1, BOUNTY_FLAG_ISLTE_ARG | BOUNTY_FLAG_NOT_BOOLY);
          collect(3, BOUNTY_FLAG_ISLTE_ARG | BOUNTY_FLAG_NOT_BOOLY);
          collect(5, BOUNTY_FLAG_OTHER);
          pc += SIZEOF_VVV;
          break;

        case ML_MINUS:
        case ML_DIV:
          collect(1, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(3, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(5, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          pc += SIZEOF_VVV;
          break;

        case ML_ISALL:
          let ilen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < ilen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_ISALL_ARG);
          }
          collect(SIZEOF_C + ilen * 2, BOUNTY_FLAG_ISALL_RESULT); // R
          pc += SIZEOF_C + ilen * 2 + 2;
          break;

        case ML_ISNALL:
        case ML_ISNONE:
          let mlen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < mlen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER);
          }
          collect(SIZEOF_C + mlen * 2, BOUNTY_FLAG_OTHER);
          pc += SIZEOF_C + mlen * 2 + 2;
          break;

        case ML_SUM:
          // TODO: collect multiple occurrences of same var once
          let splen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < splen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          }
          collect(SIZEOF_C + splen * 2, BOUNTY_FLAG_SUM_RESULT | BOUNTY_FLAG_NOT_BOOLY); // R
          pc += SIZEOF_C + splen * 2 + 2;
          break;

        case ML_PRODUCT:
          // TODO: collect multiple occurrences of same var once
          let plen = ml_dec16(ml, pc + 1);
          for (let i = 0; i < plen; ++i) {
            collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          }
          collect(SIZEOF_C + plen * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY); // R
          pc += SIZEOF_C + plen * 2 + 2;
          break;

        case ML_START:
          if (pc !== 0) return THROW(' ! compiler problem @', pcStart);
          ++pc;
          break;

        case ML_STOP:
          return;

        case ML_NOBOOL:
          // for testing, consider vars under nobool explicitly not-booly
          collect(1, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          pc += SIZEOF_V;
          break;
        case ML_NOLEAF:
          // should prevent trivial eliminations because ML_NOLEAF is never part of a trick
          // vars under ML_NOLEAF are explicitly never considered leaf vars because their counts is inflated
          collect(1, BOUNTY_FLAG_OTHER);
          pc += SIZEOF_V;
          break;

        case ML_JMP:
          pc += SIZEOF_V + ml_dec16(ml, pc + 1);
          break;
        case ML_JMP32:
          pc += SIZEOF_W + ml_dec32(ml, pc + 1);
          break;

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

        default:
          // put in a switch in the default so that the main switch is smaller. this second switch should never hit.
          getTerm().error('(cnt) unknown op', pc, ' at', pc);
          ml_throw(ml, pc, '(bnt) expecting bounty to run after the minifier and these ops should be gone');
      }
    }
    ml_throw(ml, pc, 'ML OOB');
  }

  function getDeadCount(varMeta) {
    let count = 0;
    for (let i = 0; i < varCount; i += BOUNTY_SIZEOF_VAR) {
      if (!varMeta[i]) ++count;
    }
    return count;
  }

  function getLeafCount(varMeta) {
    let count = 0;
    for (let i = 0; i < varCount; i += BOUNTY_SIZEOF_VAR) {
      if (varMeta[i] === 1) ++count;
    }
    return count;
  }

  function getOccurrenceCount(varMeta) {
    // should be eliminated when not used by ASSERTs
    let count = {};
    for (let i = 0; i < varCount; i += BOUNTY_SIZEOF_VAR) {
      count[varMeta[i]] = ~-count[varMeta[i]];
    }

    return count;
  }
}

function bounty_getCounts(bounty, varIndex) {
  return bounty[varIndex * BOUNTY_SIZEOF_VAR];
}

function bounty_markVar(bounty, varIndex) {
  ASSERT(typeof bounty === 'object', 'bounty should be object');
  ASSERT(typeof varIndex === 'number' && varIndex >= 0, 'should be valid varIndex');

  // until next loop, ignore this var (need to refresh bounty data)
  TRACE(' - bounty_markVar', varIndex);
  bounty[varIndex * BOUNTY_SIZEOF_VAR] = 0;
}

function bounty_getMeta(bounty, varIndex, _debug) {
  ASSERT(bounty_getCounts(bounty, varIndex) > 0 || _debug, 'check caller (2), this is probably a bug (var did not appear in any constraint, or its a constant, or this data was marked as stale)');
  return _dec32(bounty, varIndex * BOUNTY_SIZEOF_VAR + BOUNTY_LINK_COUNT);
}

function bounty_updateMeta(bounty, varIndex, newFlags) {
  bounty[varIndex * BOUNTY_SIZEOF_VAR + BOUNTY_LINK_COUNT] = newFlags;
}

function bounty_getOffset(bounty, varIndex, n, _debug) {
  ASSERT(bounty_getCounts(bounty, varIndex) > 0 || _debug, 'check caller (1), this is probably a bug (var did not appear in any constraint, or its a constant, or this data was marked as stale)', varIndex, n, bounty_getCounts(bounty, varIndex), _debug);
  ASSERT(n < bounty_getCounts(bounty, varIndex), 'check caller, this is probably a bug (should not get an offset beyond the count)');
  ASSERT(n < BOUNTY_MAX_OFFSETS_TO_TRACK, 'OOB, shouldnt exceed the max offset count', n, '<', BOUNTY_MAX_OFFSETS_TO_TRACK);
  return _dec32(bounty, varIndex * BOUNTY_SIZEOF_VAR + BOUNTY_SIZEOF_HEADER + n * BOUNTY_BYTES_PER_OFFSET);
}

function bounty__debug(bounty, varIndex, full) {
  let count = bounty_getCounts(bounty, varIndex);
  let r = `{B: index=${varIndex}, counts=${count}, meta=${bounty__debugMeta(bounty, varIndex)}`;
  if (full) {
    r += ', offsets:[';
    for (let i = 0; i < BOUNTY_MAX_OFFSETS_TO_TRACK; ++i) {
      if (i) r += ', ';
      if (i >= count) r += '(';
      r += _dec32(bounty, varIndex * BOUNTY_SIZEOF_VAR + BOUNTY_SIZEOF_HEADER + i * BOUNTY_BYTES_PER_OFFSET);
      if (i >= count) r += ')';
    }
    r += ']';
  }
  return r + '}';
}


function bounty__debugMeta(bounty, index) {
  ASSERT(typeof bounty === 'object', 'bounty object');
  ASSERT(typeof index === 'number', 'the index should be a number', index);
  let counts = bounty_getCounts(bounty, index) | 0; // constants would return undefined here
  if (counts === 0) return '[ constant or marked var ]';
  let meta = counts && bounty_getMeta(bounty, index, true);
  return _bounty__debugMeta(meta);
}
function _bounty__debugMeta(meta) {
  ASSERT(typeof meta === 'number', 'the meta should be a number', meta);
  let s = '0'.repeat(32 - meta.toString(2).length) + meta.toString(2);
  let what = [];

  if (!meta) what.push('BOUNTY_NONE');
  if ((meta & BOUNTY_FLAG_NOT_BOOLY) === BOUNTY_FLAG_NOT_BOOLY) {
    what.push('NOT_BOOLY');
  } else {
    what.push('BOOLY');
  }

  if ((meta & BOUNTY_FLAG_OTHER) === BOUNTY_FLAG_OTHER) what.push('OTHER');
  if ((meta & BOUNTY_FLAG_LTE_LHS) === BOUNTY_FLAG_LTE_LHS) what.push('LTE_LHS');
  if ((meta & BOUNTY_FLAG_LTE_RHS) === BOUNTY_FLAG_LTE_RHS) what.push('LTE_RHS');
  if ((meta & BOUNTY_FLAG_ISALL_ARG) === BOUNTY_FLAG_ISALL_ARG) what.push('ISALL_ARG');
  if ((meta & BOUNTY_FLAG_ISALL_RESULT) === BOUNTY_FLAG_ISALL_RESULT) what.push('ISALL_RESULT');
  if ((meta & BOUNTY_FLAG_IMP_LHS) === BOUNTY_FLAG_IMP_LHS) what.push('IMP_LHS');
  if ((meta & BOUNTY_FLAG_IMP_RHS) === BOUNTY_FLAG_IMP_RHS) what.push('IMP_RHS');
  if ((meta & BOUNTY_FLAG_ISLTE_ARG) === BOUNTY_FLAG_ISLTE_ARG) what.push('ISLTE_ARG');
  if ((meta & BOUNTY_FLAG_ISSAME_ARG) === BOUNTY_FLAG_ISSAME_ARG) what.push('ISSAME_ARG');
  if ((meta & BOUNTY_FLAG_ISSAME_RESULT) === BOUNTY_FLAG_ISSAME_RESULT) what.push('ISSAME_RESULT');
  if ((meta & BOUNTY_FLAG_ISSOME_RESULT) === BOUNTY_FLAG_ISSOME_RESULT) what.push('ISSOME_RESULT');
  if ((meta & BOUNTY_FLAG_NALL) === BOUNTY_FLAG_NALL) what.push('NALL');
  if ((meta & BOUNTY_FLAG_DIFF) === BOUNTY_FLAG_DIFF) what.push('DIFF');
  if ((meta & BOUNTY_FLAG_SOME) === BOUNTY_FLAG_SOME) what.push('SOME');
  if ((meta & BOUNTY_FLAG_SUM_RESULT) === BOUNTY_FLAG_SUM_RESULT) what.push('SUM_RESULT');
  if ((meta & BOUNTY_FLAG_XOR) === BOUNTY_FLAG_XOR) what.push('XOR');
  if ((meta & BOUNTY_JUST_IGNORE) === BOUNTY_JUST_IGNORE) what.push('JUST_IGNORE');

  return '[ ' + s + ': ' + what.join(', ') + ' ]';
}

function _dec32(bounty, offset) {
  ASSERT(bounty instanceof Uint8Array, 'should be Uint8Array');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < bounty.length, 'Invalid or OOB', offset, '>=', bounty.length);

  return (bounty[offset++] << 24) | (bounty[offset++] << 16) | (bounty[offset++] << 8) | bounty[offset];
}
function _enc32(bounty, offset, num) {
  ASSERT(bounty instanceof Uint8Array, 'should be Uint8Array');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < bounty.length, 'Invalid or OOB', offset, '>=', bounty.length);
  ASSERT(typeof num === 'number', 'Encoding numbers');
  ASSERT(num <= 0xffffffff, 'implement 64bit index support if this breaks', num);
  ASSERT(num >= 0, 'only expecting non-negative nums', num);

  bounty[offset++] = (num >> 24) & 0xff;
  bounty[offset++] = (num >> 16) & 0xff;
  bounty[offset++] = (num >> 8) & 0xff;
  bounty[offset] = num & 0xff;
}

// BODY_STOP

export {
  BOUNTY_NO_FLAGS,
  BOUNTY_FLAG_NOT_BOOLY,
  BOUNTY_FLAG_OTHER,

  BOUNTY_FLAG_DIFF,
  BOUNTY_FLAG_IMP_LHS,
  BOUNTY_FLAG_IMP_RHS,
  BOUNTY_FLAG_ISALL_ARG,
  BOUNTY_FLAG_ISALL_RESULT,
  BOUNTY_FLAG_ISSOME_RESULT,
  BOUNTY_FLAG_ISSAME_ARG,
  BOUNTY_FLAG_ISSAME_RESULT,
  BOUNTY_FLAG_ISLTE_ARG,
  BOUNTY_FLAG_LTE_LHS,
  BOUNTY_FLAG_LTE_RHS,
  BOUNTY_FLAG_NALL,
  BOUNTY_FLAG_SOME,
  BOUNTY_FLAG_SUM_RESULT,
  BOUNTY_FLAG_XOR,

  BOUNTY_MAX_OFFSETS_TO_TRACK,

  bounty__debug,
  bounty__debugMeta,
  bounty_collect,
  bounty_getCounts,
  bounty_getMeta,
  bounty_getOffset,
  bounty_markVar,
  bounty_updateMeta,
};
