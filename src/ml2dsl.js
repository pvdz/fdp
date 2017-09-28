// TODO: need to update this code to use getDomain and aliases and such
//
// this is an import function for config
// it converts a DSL string to a $config
// see /docs/dsl.txt for syntax
// see exporter.js to convert a config to this DSL
import {
  ASSERT,
  getTerm,
  isTracing,
  setTracing,
  TRACE,
  THROW,
} from '../../fdlib/src/helpers';
import {
  domain__debug,
  domain_getValue,
  domain_toArr,
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
  ML_ISSAME,
  ML_ISLT,
  ML_ISLTE,
  ML_ISNALL,
  ML_ISNONE,
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

  ml_throw,
} from './ml';
import {
  bounty__debugMeta,
  bounty_collect,
  bounty_getCounts,
} from './bounty';

// BODY_START

/**
 * Generate a dsl for given ml
 * Includes a full debugging output stack to investigate a problem more thoroughly
 *
 * @param {Uint8Array} ml
 * @param {Object} problem
 * @param {number[]} [bounty]
 * @param {Object} options See preSolver options
 * @returns {string}
 */
function ml2dsl(ml, problem, bounty, options) {
  TRACE('\n## ml2dsl');

  const DEBUG = !!options.debugDsl; // add debugging help in comments (domains, related constraints, occurrences, etc)
  const HASH_NAMES = !!options.hashNames; // replace all var varNames with $index$ with index in base36
  const INDEX_NAMES = !!options.indexNames; // replace all var varNames with _index_ (ignored if HASH_NAMES is true)
  const ADD_GROUPED_CONSTRAINTS = !!options.groupedConstraints; // only used when debugging

  let {
    varNames,
    domains,
    valdist,
    getDomain,
    getAlias,
    solveStack,
    targeted,
  } = problem;


  let pc = 0;
  let dsl = '';
  const LEN = ml.length;

  function toName(index) {
    if (HASH_NAMES) return '$' + index.toString(36) + '$';
    if (INDEX_NAMES) return '_' + index + '_';
    return varNames[index];
  }

  function valueOrName(a, vA) {
    if (vA >= 0) return vA;
    return toName(a);
  }

  function domainstr(A, vA) {
    if (vA >= 0) return 'lit(' + vA + ')';
    return domain__debug(A);
  }

  function counts(index) {
    let c = bounty_getCounts(bounty, index);
    if (c === undefined) return '-';
    return c;
  }

  let allParts = [];
  let partsPerVar = [];
  let varOps = [];
  let constraintCount = 0;
  m2d_innerLoop();

  if (DEBUG) {
    let varDecls = [];
    let varsLeft = 0;
    let aliases = 0;
    let solved = 0;
    let unsolved = 0;
    // first generate var decls for unsolved, unaliased vars
    domains.forEach((domain, index) => {
      let str = '';
      if (domain === false || (bounty && !counts(index))) {
        // either solved, alias, or leaf. leafs still needs to be updated after the rest solves.
        domain = getDomain(index);
        if (domain_getValue(domain) >= 0) {
          ++solved;
        } else {
          ++aliases;
        }
      } else {
        ++varsLeft;
        ASSERT(domain === getDomain(index), 'if not aliased then it should return this', index, domain);
        ASSERT(domain_getValue(domain) < 0, 'solved vars should be aliased to their constant');
        ++unsolved;
        str = ': ' + toName(index) + ' [' + domain_toArr(domain) + ']';

        let vardist = valdist[index];
        if (vardist) {
          switch (vardist.valtype) {
            case 'max':
            case 'mid':
            case 'min':
            case 'naive':
              str += ' @' + vardist.valtype;
              break;
            case 'list':
              str += ' @' + vardist.valtype;
              str += ' prio(' + vardist.list + ')';
              break;
            case 'markov':
              str += ' # skipping markov dist (no longer supported)';
              break;
            case 'minMaxCycle':
            case 'splitMax':
            case 'splitMin':
            default:
              THROW('unknown var dist [' + vardist.valtype + '] ' + JSON.stringify(vardist));
          }
        }
      }
      varDecls[index] = str;
    });

    let varDeclsString = domains
      .map((_, varIndex) => {
        // ignore constants, aliases, and leafs
        if (domains[varIndex] === false) return '';
        let cnts = counts(varIndex);
        if (!cnts) return '';

        let decl = varDecls[varIndex];
        ASSERT(varOps[varIndex], 'anything that has counts should have varOps of those constraints', 'var index:', varIndex, 'counts:', cnts, ', varops:', varOps[varIndex], ', decls:', decl, ', name:', varNames[varIndex], ', ppv:', partsPerVar[varIndex], '->', partsPerVar[varIndex] && partsPerVar[varIndex].map(partIndex => allParts[partIndex]));
        ASSERT(decl, 'anything that has counts should have that many constraints', 'var index:', varIndex, 'counts:', cnts, ', varops:', varOps[varIndex], ', decls:', decl, ', name:', varNames[varIndex], ', ppv:', partsPerVar[varIndex]);


        let ops = varOps[varIndex].split(/ /g).sort().join(' ');

        return (
          decl +
          ' # T:' + targeted[varIndex] + ' ' +
          ' # ocounts: ' + cnts +
          ((HASH_NAMES || !INDEX_NAMES) ? '  # index = ' + varIndex : '') +
          '  # ops (' + (ops.replace(/[^ ]/g, '').length + 1) + '): ' + ops + ' $ meta: ' + bounty__debugMeta(bounty, varIndex) +
          ((ADD_GROUPED_CONSTRAINTS && partsPerVar[varIndex])
            ? '\n ## ' + (partsPerVar[varIndex].map(partIndex => allParts[partIndex]).join(' ## '))
            : ''
          )
        );
      })
      .filter(s => !!s)
      .join('\n');

    dsl = `
# Constraints: ${constraintCount} x
# Vars: ${domains.length} x
#   Aliases: ${aliases} x
#   Domained: ${varsLeft} x
#    - Solved: ${solved} x
#    - Unsolved: ${unsolved} x
#    - Solve stack: ${solveStack.length} x (or ${solveStack.length - aliases} x without aliases)
`;
    getTerm().error(dsl);

    dsl += `
# Var decls:
${varDeclsString}

`;
  } else {
    dsl += '# vars (' + domains.length + 'x total):\n';
    dsl += domains.map((d, i) => [d, i]).filter(a => a[0] !== false).filter(a => !bounty || counts(a[1]) > 0).map(a => ': ' + toName(a[1]) + ' [' + domain_toArr(a[0]) + ']').join('\n');
    dsl += '\n\n';
  }

  dsl += '\n# Constraints (' + allParts.length + 'x):\n' + allParts.join('');

  dsl += '\n# Meta:\n' +
    m2d_getTargetsDirective() +
  '';

  return dsl;

  // ###########################################

  function m2d_dec16() {
    ASSERT(pc < LEN - 1, 'OOB');
    TRACE(' . dec16 decoding', ml[pc] << 8, 'from', pc, 'and', ml[pc + 1], 'from', pc + 1, '=>', (ml[pc] << 8) | ml[pc + 1]);
    let s = (ml[pc++] << 8) | ml[pc++];
    return s;
  }

  function m2d_dec32() {
    ASSERT(pc < LEN - 1, 'OOB');
    TRACE(' . dec32 decoding', ml[pc], ml[pc + 1], ml[pc + 2], ml[pc + 3], 'from', pc, '=>', (ml[pc] << 8) | ml[pc + 1]);
    return (ml[pc++] << 24) | (ml[pc++] << 16) | (ml[pc++] << 8) | ml[pc++];
  }

  function m2d_decA(op, skipIfConstant) {
    ASSERT(typeof op === 'string' && op, 'op should be string');

    let a = getAlias(m2d_dec16());
    let A = getDomain(a);
    let vA = domain_getValue(A);
    if (vA >= 0 && skipIfConstant) return false;

    if (DEBUG) {
      if (vA < 0) {
        if (!partsPerVar[a]) partsPerVar[a] = [];
        partsPerVar[a].push(allParts.length);
        varOps[a] = (varOps[a] === undefined ? '' : varOps[a] + ' ') + op;
      }

      let s = valueOrName(a, vA);
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + domainstr(A, vA);
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# args: ' + a;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + counts(a) + ' ';
      s += ' \n';

      return s;
    } else {
      return valueOrName(a, vA);
    }
  }

  function _m2d_decAb(op, a, b) {
    let A = getDomain(a);
    let vA = domain_getValue(A);

    let B = getDomain(b);
    let vB = domain_getValue(B);

    return __m2d_decAb(op, a, A, vA, b, B, vB);
  }
  function __m2d_decAb(op, a, A, vA, b, B, vB) {
    if (DEBUG) {
      if (vA < 0) { // else is probably dead code; all binary void constraints with a constant get resolved immediately
        if (!partsPerVar[a]) partsPerVar[a] = [];
        partsPerVar[a].push(allParts.length);
        varOps[a] = (varOps[a] === undefined ? '' : varOps[a] + ' ') + op;
      }

      if (vB < 0) { // else is probably dead code; all binary void constraints with a constant get resolved immediately
        if (!partsPerVar[b]) partsPerVar[b] = [];
        partsPerVar[b].push(allParts.length);
        varOps[b] = (varOps[b] === undefined ? '' : varOps[b] + ' ') + op;
      }

      let s = valueOrName(a, vA) + ' ' + op + ' ' + valueOrName(b, vB);
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + domainstr(A, vA) + ' ' + op + ' ' + domainstr(B, vB);
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# args: ' + a + ', ' + b;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + counts(a) + ' ' + op + ' ' + counts(b) + ' ';
      s += ' \n';

      return s;
    } else {
      return valueOrName(a, vA) + ' ' + op + ' ' + valueOrName(b, vB) + '\n';
    }
  }

  function m2d_decAbc(op) {
    ASSERT(typeof op === 'string' && op, 'op should be string');
    let a = getAlias(m2d_dec16());
    let b = getAlias(m2d_dec16());
    let c = getAlias(m2d_dec16());
    return _m2d_decAbc(op, a, b, c);
  }
  function _m2d_decAbc(op, a, b, c) {
    let A = getDomain(a);
    let vA = domain_getValue(A);

    let B = getDomain(b);
    let vB = domain_getValue(B);

    let C = getDomain(c);
    let vC = domain_getValue(C);

    return __m2d_decAbc(op, a, A, vA, b, B, vB, c, C, vC);
  }
  function __m2d_decAbc(op, a, A, vA, b, B, vB, c, C, vC) {
    if (DEBUG) {
      if (vA < 0) { // else is probably dead; args are ordered and A can only be solved if B is also solved or unordered.
        if (!partsPerVar[a]) partsPerVar[a] = [];
        partsPerVar[a].push(allParts.length);
        varOps[a] = (varOps[a] === undefined ? '' : varOps[a] + ' ') + op;
      }

      if (vB < 0) {
        if (!partsPerVar[b]) partsPerVar[b] = [];
        partsPerVar[b].push(allParts.length);
        varOps[b] = (varOps[b] === undefined ? '' : varOps[b] + ' ') + op;
      }

      if (vC < 0) {
        if (!partsPerVar[c]) partsPerVar[c] = [];
        partsPerVar[c].push(allParts.length);
        varOps[c] = (varOps[c] === undefined ? '' : varOps[c] + ' ') + op;
      }

      let s = valueOrName(c, vC) + ' = ' + valueOrName(a, vA) + ' ' + op + ' ' + valueOrName(b, vB);
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + domainstr(C, vC) + ' = ' + domainstr(A, vA) + ' ' + op + ' ' + domainstr(B, vB);
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# indexes: ' + c + ' = ' + a + ' ' + op + ' ' + b;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + counts(c) + ' = ' + counts(a) + ' ' + op + ' ' + counts(b) + ' ';
      s += '\n';

      return s;
    } else {
      return valueOrName(c, vC) + ' = ' + valueOrName(a, vA) + ' ' + op + ' ' + valueOrName(b, vB) + '\n';
    }
  }

  function m2d_listVoid(callName) {
    ASSERT(typeof callName === 'string' && callName, 'callName should be string');

    let argCount = m2d_dec16();

    if (argCount === 2) {
      if (callName === 'all') return _m2d_decAb('&', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'diff') return _m2d_decAb('!=', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'imp') return _m2d_decAb('->', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'lt') return _m2d_decAb('<', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'lte') return _m2d_decAb('<=', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'nall') return _m2d_decAb('!&', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'nimp') return _m2d_decAb('!->', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      //if (callName === 'none') return _m2d_decAb('!|', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'same') return _m2d_decAb('==', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'some') return _m2d_decAb('|', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'xnor') return _m2d_decAb('!^', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'xor') return _m2d_decAb('^', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
    }

    let indexes = '';
    let counters = '';
    let argNames = '';
    let debugs = '';
    //let prevIndex = -1;
    for (let i = 0; i < argCount; ++i) {
      let d = getAlias(m2d_dec16());
      let D = getDomain(d);
      let vD = domain_getValue(D);

      argNames += valueOrName(d, vD) + ' ';
      if (DEBUG) {
        if (vD < 0) {
          if (!partsPerVar[d]) partsPerVar[d] = [];
          partsPerVar[d].push(allParts.length);
          varOps[d] = (varOps[d] === undefined ? '' : varOps[d] + ' ') + callName;
        }

        indexes += d + ' ';
        if (bounty) counters += counts(d) + ' ';
        debugs += domainstr(D, vD) + ' ';
      }
    }
    if (DEBUG) {
      let s = callName + '( ' + argNames + ')';
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + callName + '( ' + debugs + ') ';
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# indexes: ' + indexes;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + callName + '( ' + counters + ')';
      s += '\n';

      return s;
    } else {
      return callName + '( ' + argNames + ')\n';
    }
  }

  function m2d_listResult(callName) {
    ASSERT(typeof callName === 'string' && callName, 'callName should be string');

    let argCount = m2d_dec16();
    return m2d_listResultBody(callName, argCount);
  }
  function m2d_listResultBody(callName, argCount) {
    ASSERT(typeof callName === 'string' && callName, 'callName should be string');

    if (argCount === 2) {
      //if (callName === 'all?') return _m2d_decAbc('&?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'diff?') return _m2d_decAbc('!=?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      //if (callName === 'nall?') return _m2d_decAbc('!&?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      //if (callName === 'none?') return _m2d_decAbc('!|?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'same?') return _m2d_decAbc('==?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      //if (callName === 'some?') return _m2d_decAbc('|?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'sum') return _m2d_decAbc('+', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'product') return _m2d_decAbc('*', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
    }

    let indexes = '';
    let counters = '';
    let argNames = '';
    let debugs = '';
    //let prevIndex = -1;
    for (let i = 0; i < argCount; ++i) {
      let d = getAlias(m2d_dec16());
      let D = getDomain(d);
      let vD = domain_getValue(D);

      argNames += valueOrName(d, vD) + ' ';
      if (DEBUG) {
        if (vD < 0) {
          if (!partsPerVar[d]) partsPerVar[d] = [];
          partsPerVar[d].push(allParts.length);
          varOps[d] = (varOps[d] === undefined ? '' : varOps[d] + ' ') + callName;
        }

        indexes += d + ' ';
        if (bounty) counters += counts(d) + ' ';
        debugs += domainstr(D, vD) + ' ';
      }
    }

    let r = getAlias(m2d_dec16());
    let R = getDomain(r);
    let vR = domain_getValue(R);

    if (DEBUG) {
      if (vR < 0) {
        if (!partsPerVar[r]) partsPerVar[r] = [];
        partsPerVar[r].push(allParts.length);
        varOps[r] = (varOps[r] === undefined ? '' : varOps[r] + ' ') + callName;
      }

      let s = valueOrName(r, vR) + ' = ' + callName + '( ' + argNames + ')';
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + domainstr(R, vR) + ' = ' + callName + '( ' + debugs + ') ';
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# indexes: ' + r + ' = ' + indexes;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + counts(r) + ' = ' + callName + '( ' + counters + ')';
      s += '\n';

      return s;
    } else {
      return valueOrName(r, vR) + ' = ' + callName + '( ' + argNames + ')\n';
    }
  }

  function m2d_innerLoop() {
    while (pc < LEN) {
      let pcStart = pc;

      let op = ml[pc++];
      let part = '';

      switch (op) {
        case ML_START:
        case ML_STOP:
        case ML_NOBOOL:
        case ML_NOLEAF:
        case ML_NOOP:
        case ML_NOOP2:
        case ML_NOOP3:
        case ML_NOOP4:
        case ML_JMP:
        case ML_JMP32:
          break;
        default:
          ++constraintCount;
      }

      switch (op) {
        case ML_START:
          if (pc !== 1) { // pc is already incremented...
            return THROW(' ! ml2dsl compiler problem @', pcStart);
          }
          break;

        case ML_STOP:
          TRACE(' ! good end @', pcStart);
          return;

        case ML_JMP:
          let delta = m2d_dec16();
          TRACE(' ! jmp', delta);
          if (delta <= 0) THROW('Must jump some bytes');
          pc += delta;
          break;
        case ML_JMP32:
          let delta32 = m2d_dec32();
          TRACE(' ! jmp32', delta32);
          if (delta32 <= 0) THROW('Must jump some bytes');
          pc += delta32;
          break;

        case ML_LT:
          TRACE(' ! lt');
          part = m2d_listVoid('lt');
          break;
        case ML_LTE:
          TRACE(' ! lte');
          part = m2d_listVoid('lte');
          break;
        case ML_XOR:
          TRACE(' ! xor');
          part = m2d_listVoid('xor');
          break;
        case ML_IMP:
          TRACE(' ! imp vv');
          part = m2d_listVoid('imp');
          break;
        case ML_NIMP:
          TRACE(' ! nimp vv');
          part = m2d_listVoid('nimp');
          break;

        case ML_ALL:
          TRACE(' ! all');
          part = m2d_listVoid('all');
          break;
        case ML_DIFF:
          TRACE(' ! diff');
          part = m2d_listVoid('diff');
          break;
        case ML_NALL:
          TRACE(' ! nall');
          part = m2d_listVoid('nall');
          break;
        case ML_NONE:
          TRACE(' ! none');
          part = m2d_listVoid('none');
          break;
        case ML_SAME:
          TRACE(' ! same');
          part = m2d_listVoid('same');
          break;
        case ML_SOME:
          TRACE(' ! some');
          part = m2d_listVoid('some');
          break;
        case ML_XNOR:
          TRACE(' ! xnor');
          part = m2d_listVoid('xnor');
          break;

        case ML_ISLT:
          TRACE(' ! islt vvv');
          part = m2d_decAbc('<?');
          break;
        case ML_ISLTE:
          TRACE(' ! islte vvv');
          part = m2d_decAbc('<=?');
          break;

        case ML_ISALL:
          TRACE(' ! isall');
          part = m2d_listResult('all?');
          break;
        case ML_ISDIFF:
          TRACE(' ! isdiff');
          part = m2d_listResult('diff?');
          break;
        case ML_ISNALL:
          TRACE(' ! isnall');
          part = m2d_listResult('nall?');
          break;
        case ML_ISNONE:
          TRACE(' ! isnone');
          part = m2d_listResult('none?');
          break;
        case ML_ISSAME:
          TRACE(' ! issame');
          part = m2d_listResult('same?');
          break;
        case ML_ISSOME:
          TRACE(' ! issome');
          part = m2d_listResult('some?');
          break;

        case ML_MINUS:
          TRACE(' ! minus');
          part = m2d_decAbc('-');
          break;
        case ML_DIV:
          TRACE(' ! div');
          part = m2d_decAbc('/');
          break;

        case ML_SUM:
          TRACE(' ! sum');
          part = m2d_listResult('sum');
          break;
        case ML_PRODUCT:
          TRACE(' ! product');
          part = m2d_listResult('product');
          break;

        case ML_NOBOOL:
          TRACE(' ! nobool');
          // fdq will understand but ignore this. skip for constants.
          let Bpart = m2d_decA('<debug>', true);
          if (Bpart !== false) part = '@custom nobool ' + Bpart + '\n';
          break;
        case ML_NOLEAF:
          TRACE(' ! noleaf');
          // fdq will understand but ignore this. skip for constants.
          let Apart = m2d_decA('<debug>', true);
          if (Apart !== false) {
            part = '@custom noleaf ' + Apart + '\n';
          }
          break;
        case ML_NOOP:
          TRACE(' ! noop');
          pc = pcStart + 1;
          break;
        case ML_NOOP2:
          TRACE(' ! noop 2');
          pc = pcStart + 2;
          break;
        case ML_NOOP3:
          TRACE(' ! noop 3');
          pc = pcStart + 3;
          break;
        case ML_NOOP4:
          TRACE(' ! noop 4');
          pc = pcStart + 4;
          break;

        default:
          ml_throw('(m2d) unknown op', pc, ' at', pc);
      }
      allParts.push(part);
    }
  }

  function m2d_getTargetsDirective() {
    let targets = [];
    let targeted = problem.targeted;
    let len = domains.length;
    let total = 0;
    let nontargets = 0;
    for (let i = 0; i < len; ++i) {
      if (domains[i] === false) continue;
      if (!counts(i)) continue;

      ++total;
      if (!targeted[i]) {
        ++nontargets; // we only care about this state for vars that will appear in the dsl.
        continue;
      }

      targets.push(toName(i));
    }

    // TODO
    // what if there are no targets left? we could set internal
    // vars to anything but that could still affect targeted
    // vars through the solve stack... or perhaps they are irrelevant?
    // does this mean any valuation will work to resolve the vars?

    return '@custom targets' + ((nontargets && nontargets.length) ? '( ' + targets.join(' ') + ' )' : ' all') + ' # ' + (total - nontargets) + ' / ' + total + '\n';
  }
}

function m2d__debug(problem, notTrace) {
  TRACE('\nm2d__debug, temporarily disabling TRACE while generating dsl');
  let was = isTracing();
  if (!was && !notTrace) return ''; // TRACE is disabled; dont generate anything as it wont be seen (reduce test runtime)
  // __REMOVE_BELOW_FOR_ASSERTS__
  setTracing(false);
  // __REMOVE_ABOVE_FOR_ASSERTS__
  let dsl = ml2dsl(problem.ml, problem, bounty_collect(problem.ml, problem), {debugDsl: false, hashNames: false});
  // __REMOVE_BELOW_FOR_ASSERTS__
  setTracing(was);
  // __REMOVE_ABOVE_FOR_ASSERTS__

  return '\n## current remaining problem as dsl:\n' + dsl + '## end of current remaining problem\n';
}

// BODY_STOP

export {
  ml2dsl,
  m2d__debug,
};
