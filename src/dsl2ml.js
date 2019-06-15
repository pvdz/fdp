// this is an import function for config
// it converts a DSL string to a $config
// see /docs/dsl.txt for syntax
// see exporter.js to convert a config to this DSL
import {
  SUB,
  SUP,
  ASSERT,
  getTerm,
  TRACE,
} from '../../fdlib/src/helpers';
import {
  domain_createRange,
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

  SIZEOF_V,
  SIZEOF_W,
} from './ml';

// BODY_START

// ords (number matching is faster, especially since we use a buffer anyways)
const $$AND = 38;
const $$AT = 64;
const $$BANG = 33;
const $$COLON = 58;
const $$COMMA = 44;
const $$CR = 10;
const $$LF = 13;
const $$DASH = 45;
const $$DIV = 47;
const $$EQ = 61;
const $$GT = 62;
const $$HASH = 35;
const $$LEFTBRACK = 91;
const $$LEFTPAREN = 40;
const $$LT = 60;
const $$OR = 124;
const $$PLUS = 43;
const $$QM = 63;
const $$SPACE = 32;
const $$RIGHTBRACK = 93;
const $$RIGHTPAREN = 41;
const $$SQUOTE = 39;
const $$STAR = 42;
const $$TAB = 9;
const $$XOR = 94;
const $$0 = 48;
const $$1 = 49;
const $$2 = 50;
const $$3 = 51;
const $$4 = 52;
const $$5 = 53;
const $$6 = 54;
const $$7 = 55;
const $$8 = 56;
const $$9 = 57;
const $$a = 97;
const $$c = 99;
const $$d = 100;
const $$e = 101;
const $$f = 102;
const $$g = 103;
const $$i = 105;
const $$l = 108;
const $$m = 109;
const $$n = 110;
const $$o = 111;
const $$p = 112;
const $$r = 114;
const $$s = 115;
const $$t = 116;
const $$x = 120;
const $$z = 122;
const $$A = 65;
const $$Z = 98;

/**
 * Compile the constraint dsl to a bytecode
 *
 * @param {string} dslStr
 * @param {Object} problem
 * @param {boolean} [_debug] Improved error reporting when true
 * @returns {string}
 */
function dsl2ml(dslStr, problem, _debug) {
  TRACE('# dsl2ml:', [dslStr.slice(0, 100).replace(/ +/g, ' ') + (dslStr.replace(/ +/g, ' ').length > 100 ? '...' : '')]);

  problem.input.varstrat = 'default';
  problem.input.valstrat = 'default';
  problem.input.dsl = dslStr;

  let {
    addVar,
    setDomain,
    name2index,
  } = problem;

  let constraints = 0;
  let freeDirective = -1; // for `@custom free x`. this var tries to ensure exactly x bytes are "free"

  let dslPointer = 0;

  let dslBuf;
  if (typeof Buffer === 'undefined') {
    dslBuf = new window.TextEncoder('utf-8').encode(dslStr);
  } else {
    dslBuf = new Uint8Array(Buffer.from(dslStr, 'binary'));
  }
  ASSERT(dslBuf instanceof Uint8Array);
  let len = dslBuf.length;

  let mlBufSize = Math.ceil(dslBuf.length / 5); // 20% is arbitrary choice. grown dynamically when needed
  let mlBuffer = new Uint8Array(mlBufSize).fill(0);
  let mlPointer = 0;

  // this is for a hack
  let lastAssignmentIndex = -1;
  let lastUnknownIndex = -1;

  encode8bit(ML_START);

  while (!isEof()) parseStatement();

  if (freeDirective > 0) {
    // compile a jump of given size. this will be considered available space
    TRACE('forcing', freeDirective, 'bytes of available space');
    compileJump(freeDirective);
  }

  encode8bit(ML_STOP); // this step will be undone but serves to ensure the buffer isnt grown in the actual compilation step (which happens after the available-space-checks)
  --mlPointer;

  if (freeDirective < 0) {
    // compile a jump for the remainder of the space, if any, which could be used by the recycle mechanisms
    // only do this here when the free directive is absent
    let leftFree = (mlBufSize - mlPointer) - 1; // STOP will occupy 1 byte
    TRACE('space available', leftFree, 'bytes');
    if (leftFree > 0) compileJump(leftFree);
  }

  encode8bit(ML_STOP); // put the STOP at the end

  // if there is now still space left, we need to crop it because freeDirective was set and didnt consume it all
  if (mlBufSize - mlPointer) {
    TRACE('cropping excess available space', mlBufSize, mlPointer, mlBufSize - mlPointer);
    // if the free directive was given, remove any excess free space
    // note that one more byte needs to be compiled after this (ML_STOP)
    mlBuffer = mlBuffer.slice(0, mlPointer);
  }
  ASSERT(mlPointer === mlBuffer.length, 'mlPointer should now be at the first unavailable cell of the buffer', mlPointer, mlBuffer.length, mlBuffer);

  problem.ml = mlBuffer;
  if (!problem.input.targets) problem.input.targets = 'all';

  getTerm().log('# dsl2ml: parsed', constraints, 'constraints and', problem.domains.length, 'vars');
  return;

  // ########################################################################

  function startConstraint(op) {
    ++constraints;
    encode8bit(op);
  }

  function encode8bit(num) {
    ASSERT(typeof num === 'number' && num >= 0 && num <= 0xff, 'OOB number');
    TRACE('encode8bit:', num, 'dsl pointer:', dslPointer, ', ml pointer:', mlPointer);

    if (mlPointer >= mlBufSize) grow();

    mlBuffer[mlPointer++] = num;
  }

  function encode16bit(num) {
    TRACE('encode16bit:', num, '->', num >> 8, num & 0xff, 'dsl pointer:', dslPointer, ', ml pointer:', mlPointer, '/', mlBufSize);
    ASSERT(typeof num === 'number', 'Encoding 16bit must be num', typeof num, num);
    ASSERT(num >= 0, 'OOB num', num);
    if (num > 0xffff) THROW('Need 32bit num support but missing it', num);

    if (mlPointer >= mlBufSize - 1) grow();

    mlBuffer[mlPointer++] = (num >> 8) & 0xff;
    mlBuffer[mlPointer++] = num & 0xff;
  }

  function encode32bit(num) {
    TRACE('encode32bit:', num, '->', (num >> 24) & 0xff, (num >> 16) & 0xff, (num >> 8) & 0xff, num & 0xff, 'dsl pointer:', dslPointer, ', ml pointer:', mlPointer);
    ASSERT(typeof num === 'number', 'Encoding 32bit must be num', typeof num, num);
    ASSERT(num >= 0, 'OOB num', num);
    if (num > 0xffffffff) THROW('This requires 64bit support', num);

    if (mlPointer >= mlBufSize - 3) grow();

    mlBuffer[mlPointer++] = (num >> 24) & 0xff;
    mlBuffer[mlPointer++] = (num >> 16) & 0xff;
    mlBuffer[mlPointer++] = (num >> 8) & 0xff;
    mlBuffer[mlPointer++] = num & 0xff;
  }

  function grow(forcedExtraSpace) {
    TRACE(' - grow(' + (forcedExtraSpace || '') + ') from', mlBufSize);
    // grow the buffer by 10% or `forcedExtraSpace`
    // you can't really grow existing buffers, instead you create a bigger buffer and copy the old one into it...
    let oldSize = mlBufSize;
    if (forcedExtraSpace) mlBufSize += forcedExtraSpace;
    else mlBufSize += Math.max(Math.ceil(mlBufSize * 0.1), 10);
    ASSERT(mlBufSize > mlBuffer.length, 'grow() should grow() at least a bit...', mlBuffer.length, '->', mlBufSize);

    if (typeof Buffer === 'undefined') {
      if (ArrayBuffer.transfer) mlBuffer = new Uint8Array(ArrayBuffer.transfer(mlBuffer.buffer, mlBufSize));
      else mlBuffer = new Uint8Array(ArrayBufferTransferPoly(mlBuffer.buffer, mlBufSize));
    } else {
      mlBuffer = new Uint8Array(Buffer.concat([mlBuffer], mlBufSize)); // wont actually concat, but will copy the existing buffer into a buffer of given size
      mlBuffer.fill(0, oldSize);
    }

    ASSERT(mlBuffer instanceof Uint8Array);
  }

  function read() {
    return dslBuf[dslPointer];
  }

  function readD(delta) {
    return dslBuf[dslPointer + delta];
  }

  function substr_expensive(start, stop) { // use sparingly!
    return String.fromCharCode(...dslBuf.slice(start, stop));
  }

  function skip() {
    ++dslPointer;
  }

  function is(c, desc) {
    if (!desc) desc = '';
    if (read() !== c) THROW('Expected ' + desc + ' `' + c + '`, found `' + read() + '`');
    skip();
  }

  function skipWhitespaces() {
    while (dslPointer < len && isWhitespace(read())) skip();
  }

  function skipWhites() {
    while (!isEof()) {
      let c = read();
      if (isWhite(c)) {
        skip();
      } else if (isComment(c)) {
        skipComment();
      } else {
        break;
      }
    }
  }

  function isWhitespace(s) {
    // make sure you dont actually want isNewlineChar()
    return s === $$SPACE || s === $$TAB;
  }

  function isNewlineChar(s) {
    return s === $$CR || s === $$LF;
  }
  function atEol(c) {
    return isNewlineChar(c) || isComment(c) || isEof();
  }

  function isLineEnd(s) {
    // the line ends at a newline or a comment
    return s === $$CR || s === $$LF || s === $$HASH;
  }

  function isComment(s) {
    return s === $$HASH;
  }

  function isWhite(s) {
    return isWhitespace(s) || isNewlineChar(s);
  }

  function expectEol() {
    skipWhitespaces();
    if (dslPointer < len) {
      let c = read();
      if (c === $$HASH) {
        skipComment();
      } else if (isNewlineChar(c)) {
        skip();
      } else {
        THROW('Expected EOL but got `' + read() + '`');
      }
    }
  }

  function isEof() {
    return dslPointer >= len;
  }

  function parseStatement() {
    // either:
    // - start with colon: var decl
    // - start with hash: line comment
    // - empty: empty
    // - otherwise: constraint

    skipWhites();

    ASSERT(read() !== $$HASH, 'comments should be parsed by skipWhites');
    switch (read()) {
      case $$COLON:
        parseVar();
        return;
      case $$AT:
        parseAtRule();
        return;
      default:
        if (!isEof()) {
          parseVoidConstraint();
          return;
        }
    }
  }

  function parseVar() {
    skip(); // is($$COLON)
    skipWhitespaces();
    let nameNames = parseIdentifier();
    skipWhitespaces();
    if (read() === $$COMMA) {
      nameNames = [nameNames];
      do {
        skip();
        skipWhitespaces();
        nameNames.push(parseIdentifier());
        skipWhitespaces();
      } while (!isEof() && read() === $$COMMA);
    }
    if (read() === $$EQ) {
      skip();
      skipWhitespaces();
    }
    let domain = parseDomain();
    skipWhitespaces();
    let mod = parseModifier();
    expectEol();

    if (typeof nameNames === 'string') {
      addParsedVar(nameNames, domain, mod);
    } else {
      nameNames.forEach(name => addParsedVar(name, domain, mod));
    }
  }
  function addParsedVar(name, domain, mod) {
    return addVar(name, domain, mod, false, true, THROW);
  }

  function parseIdentifier() {
    if (read() === $$SQUOTE) return parseQuotedIdentifier();
    else return parseUnquotedIdentifier();
  }

  function parseQuotedIdentifier() {
    is($$SQUOTE);

    let ident = '';
    while (!isEof()) {
      let c = read();
      if (c === $$SQUOTE) break;
      if (c !== $$HASH && isLineEnd(c)) THROW('Quoted identifier wasnt closed at eol');
      ident += String.fromCharCode(c);
      skip();
    }
    if (isEof()) THROW('Quoted identifier wasnt closed at eof');
    if (!ident) THROW('Expected to parse identifier, found none');
    skip(); // quote
    return ident; // return unquoted ident
  }

  function parseUnquotedIdentifier() {
    // anything terminated by whitespace
    let c = read();
    let ident = '';
    if (c >= $$0 && c <= $$9) THROW('Unquoted ident cant start with number');
    while (!isEof()) {
      c = read();
      if (!isValidUnquotedIdentChar(c)) break;
      ident += String.fromCharCode(c);
      skip();
    }
    if (!ident) THROW('Expected to parse identifier, found none');
    return ident;
  }

  function isValidUnquotedIdentChar(c) {
    switch (c) {
      case $$LEFTPAREN:
      case $$RIGHTPAREN:
      case $$COMMA:
      case $$LEFTBRACK:
      case $$RIGHTBRACK:
      case $$SQUOTE:
      case $$HASH:
        return false;
    }
    if (isWhite(c)) return false;
    return true;
  }

  function parseDomain() {
    // []
    // [lo hi]
    // [[lo hi] [lo hi] ..]
    // *
    // 25
    // (comma's optional and ignored)

    let domain;
    let c = read();
    switch (c) {
      case $$LEFTBRACK:

        is($$LEFTBRACK, 'domain start');
        skipWhitespaces();

        domain = [];

        if (read() === $$LEFTBRACK) { // range inside the domain that is wrapped in brakcets
          do {
            skip();
            skipWhitespaces();
            let lo = parseNumber();
            skipWhitespaces();
            if (read() === $$COMMA) {
              skip();
              skipWhitespaces();
            }
            let hi = parseNumber();
            skipWhitespaces();
            is($$RIGHTBRACK, 'range-end');
            skipWhitespaces();

            domain.push(lo, hi);

            if (read() === $$COMMA) {
              skip();
              skipWhitespaces();
            }
          } while (read() === $$LEFTBRACK);
        } else {
          // individual ranges not wrapped
          while (read() !== $$RIGHTBRACK) {
            skipWhitespaces();
            let lo = parseNumber();
            skipWhitespaces();
            if (read() === $$COMMA) {
              skip();
              skipWhitespaces();
            }
            let hi = parseNumber();
            skipWhitespaces();

            domain.push(lo, hi);

            if (read() === $$COMMA) {
              skip();
              skipWhitespaces();
            }
          }
        }

        is($$RIGHTBRACK, 'domain-end');
        if (domain.length === 0) THROW('Empty domain [] in dsl, this problem will always reject');
        return domain;

      case $$STAR:
        skip();
        return [SUB, SUP];

      case $$0:
      case $$1:
      case $$2:
      case $$3:
      case $$4:
      case $$5:
      case $$6:
      case $$7:
      case $$8:
      case $$9:
        let v = parseNumber();
        skipWhitespaces();
        return [v, v];
    }

    THROW('Expecting valid domain start, found `' + c + '`');
  }

  function parseModifier() {
    if (read() !== $$AT) return;
    skip();

    let mod = {};

    let stratName = '';
    while (true) {
      let c = read();
      if (!((c >= $$a && c <= $$z) || (c >= $$A && c <= $$Z))) break;
      stratName += String.fromCharCode(c);
      skip();
    }

    switch (stratName) {
      case 'list':
        parseList(mod);
        break;

      case 'markov':
        parseMarkov(mod);
        break;

      case 'max':
      case 'mid':
      case 'min':
      case 'naive':
        mod.valtype = stratName;
        break;

      case 'minMaxCycle':
      case 'splitMax':
      case 'splitMin':
        THROW('TODO: implement this modifier [' + stratName + ']');
        break;
      default:
        THROW('implement me (var mod) [`' + stratName + '`]');
    }

    mod.valtype = stratName;

    return mod;
  }

  function parseList(mod) {
    skipWhitespaces();

    if (!(readD(0) === $$p && readD(1) === $$r && readD(2) === $$i && readD(3) === $$o && readD(4) === $$LEFTPAREN)) {
      THROW('Expecting the priorities to follow the `@list`');
    }

    dslPointer += 5;
    mod.valtype = 'list';
    mod.list = parseNumList();

    is($$RIGHTPAREN, 'list end');
  }

  function parseMarkov(mod) {
    mod.valtype = 'markov';
    let repeat = true;
    while (repeat) {
      repeat = false;
      skipWhitespaces();
      switch (read()) {
        case $$m: // matrix
          if (readD(1) === $$a && readD(2) === $$t && readD(3) === $$r && readD(4) === $$i && readD(5) === $$x && readD(6) === $$LEFTPAREN) {
            // TOFIX: there is no validation here. apply stricter and safe matrix parsing

            dslPointer += 7;
            let start = dslPointer;
            while (read() !== $$RIGHTPAREN && !isEof()) skip();
            if (isEof()) THROW('The matrix must be closed by a `)` but did not find any');
            ASSERT(read() === $$RIGHTPAREN, 'code should only stop at eof or )');

            let matrix = substr_expensive(start, dslPointer);
            let code = 'return ' + matrix;
            let func = Function(code);
            /* eslint no-new-func: "off" */
            mod.matrix = func();

            is($$RIGHTPAREN, 'end of matrix'); // kind of a redundant double check. could also just skip() here.

            repeat = true;
          }
          break;

        case $$l: // legend
          if (readD(1) === $$e && readD(2) === $$g && readD(3) === $$e && readD(4) === $$n && readD(5) === $$d && readD(6) === $$LEFTPAREN) {
            dslPointer += 7;
            skipWhitespaces();
            mod.legend = parseNumList();
            skipWhitespaces();
            is($$RIGHTPAREN, 'legend closer');

            repeat = true;
          }
          break;

        case $$e: // expand
          if (readD(1) === $$x && readD(2) === $$p && readD(3) === $$a && readD(4) === $$n && readD(5) === $$d && readD(6) === $$LEFTPAREN) {
            dslPointer += 7;
            skipWhitespaces();
            mod.expandVectorsWith = parseNumber();
            skipWhitespaces();
            is($$RIGHTPAREN, 'expand closer');

            repeat = true;
          }
          break;
      }
    }
  }

  function skipComment() {
    is($$HASH, 'comment start'); //is('#', 'comment hash');
    while (!isEof() && !isNewlineChar(read())) skip();
    if (!isEof()) skip();
  }

  function parseVoidConstraint() {
    // parse a constraint that does not return a value itself

    // first try to parse single value constraints without value like markov() and diff()
    if (parseUexpr()) return;

    // so the first value must be a value returning expr
    parseComplexVoidConstraint();

    expectEol();
  }

  function parseComplexVoidConstraint() {
    // parse a constraint that at least starts with a Vexpr but ultimately doesnt return anything

    let indexA = parseVexpr(undefined, true);

    skipWhitespaces();
    // `A==B<eof>` then A==B would be part of A and the parser would want to parse a cop here. there's a test case.
    if (isEof()) THROW('Expected to parse a cop but reached eof instead');

    let cop = parseCop();
    skipWhitespaces();

    if (cop === '=') {
      lastAssignmentIndex = indexA;
      parseAssignment(indexA);
    } else {
      ASSERT(cop, 'the cop parser should require to parse a valid cop');
      let indexB = parseVexpr();
      compileVoidConstraint(indexA, cop, indexB);
    }
  }

  function compileVoidConstraint(indexA, cop, indexB) {
    switch (cop) {
      case '==':
        startConstraint(ML_SAME);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '!=':
        startConstraint(ML_DIFF);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '<':
        startConstraint(ML_LT);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        break;

      case '<=':
        startConstraint(ML_LTE);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        break;

      case '>':
        startConstraint(ML_LT);
        encode16bit(2);
        encode16bit(indexB);
        encode16bit(indexA);
        break;

      case '>=':
        startConstraint(ML_LTE);
        encode16bit(2);
        encode16bit(indexB);
        encode16bit(indexA);
        break;

      case '&':
        startConstraint(ML_ALL);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '!&':
        startConstraint(ML_NALL);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '|':
        startConstraint(ML_SOME);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '!|':
        startConstraint(ML_NONE);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '^':
        startConstraint(ML_XOR);
        encode16bit(2); // this brings the op size in line with all other ops. kind of a waste but so be it.
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '!^':
        startConstraint(ML_XNOR);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '->':
        startConstraint(ML_IMP);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        break;

      case '!->':
        startConstraint(ML_NIMP);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        break;

      default:
        THROW('Unknown constraint op: [' + cop + ']');
    }
  }

  function parseAssignment(indexC) {
    let indexA = parseVexpr(indexC);
    skipWhitespaces();
    let c = read();
    if (isEof() || isLineEnd(c)) {
      // any var, literal, or group without "top-level" op (`A=5`, `A=X`, `A=(B+C)`, `A=sum(...)`, etc)
      if (indexA !== indexC) {
        compileVoidConstraint(indexA, '==', indexC);
      }
    } else {
      let rop = parseRop();
      if (!rop) THROW('Expecting right paren or rop, got [' + rop + ']');
      skipWhitespaces();
      let indexB = parseVexpr();
      return compileValueConstraint(indexA, rop, indexB, indexC);
    }
  }

  function compileValueConstraint(indexA, rop, indexB, indexC) {
    let wasReifier = false;

    switch (rop) {
      case '==?':
        startConstraint(ML_ISSAME);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        encode16bit(indexC);
        wasReifier = true;
        break;

      case '!=?':
        startConstraint(ML_ISDIFF);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        encode16bit(indexC);
        wasReifier = true;
        break;

      case '<?':
        startConstraint(ML_ISLT);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        wasReifier = true;
        break;

      case '<=?':
        startConstraint(ML_ISLTE);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        wasReifier = true;
        break;

      case '&?':
        startConstraint(ML_ISALL);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '!&?':
        startConstraint(ML_ISNALL);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '|?':
        startConstraint(ML_ISSOME);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '!|?':
        startConstraint(ML_ISNONE);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '+':
        startConstraint(ML_SUM);
        encode16bit(2); // count
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        encode16bit(indexC);
        break;

      case '-':
        startConstraint(ML_MINUS);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '*':
        startConstraint(ML_PRODUCT);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        encode16bit(indexC);
        break;

      case '/':
        startConstraint(ML_DIV);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '>?':
        return compileValueConstraint(indexB, '<?', indexA, indexC);

      case '>=?':
        return compileValueConstraint(indexB, '<=?', indexA, indexC);

      default:
        THROW('Expecting right paren or rop, got [' + rop + ']');
    }

    if (wasReifier && indexC === lastAssignmentIndex && indexC === lastUnknownIndex) setDomain(indexC, domain_createRange(0, 1));

    return indexC;
  }

  function parseCop() {
    let c = read();
    switch (c) {
      case $$EQ:
        skip();
        if (read() === $$EQ) {
          skip();
          return '==';
        }
        return '=';
      case $$BANG:
        skip();
        let r = read();
        if (r === $$EQ) {
          skip();
          return '!=';
        }
        if (r === $$AND) {
          skip();
          return '!&';
        }
        if (r === $$XOR) {
          skip();
          return '!^';
        }
        if (r === $$OR) {
          skip();
          return '!|';
        }
        if (r === $$DASH && readD(1) === $$GT) {
          skip();
          skip();
          return '!->';
        }
        return THROW('Unknown cop that starts with [!]');
      case $$LT:
        skip();
        if (read() === $$EQ) {
          skip();
          return '<=';
        }
        return '<';
      case $$GT:
        skip();
        if (read() === $$EQ) {
          skip();
          return '>=';
        }
        return '>';
      case $$DASH:
        if (readD(1) === $$GT) {
          skip();
          skip();
          return '->';
        }
        break; // error
      case $$AND:
        skip();
        return '&';
      case $$OR:
        skip();
        return '|';
      case $$XOR:
        skip();
        return '^';
      case $$HASH:
        return THROW('Expected to parse a cop but found a comment instead');
    }
    if (isEof()) THROW('Expected to parse a cop but reached eof instead');
    THROW('Unknown cop char: `' + c + '`');
  }

  function parseRop() {
    switch (read()) {
      case $$EQ:
        skip();
        if (read() === $$EQ) {
          skip();
          is($$QM, 'reifier suffix');
          return '==?';
        } else {
          return '=';
        }

      case $$BANG:
        skip();
        let r = '';
        if (read() === $$EQ) {
          is($$EQ, 'middle part of !=? op');
          r = '!=?';
        } else if (read() === $$AND) {
          is($$AND, 'middle part of !&? op');
          r = '!&?';
        } else if (read() === $$OR) {
          is($$OR, 'middle part of !|? op');
          r = '!|?';
        } else {
          THROW('invalid rop that starts with a bang');
        }
        is($$QM, 'reifier suffix');
        return r;

      case $$LT:
        skip();
        if (read() === $$EQ) {
          skip();
          is($$QM, 'reifier suffix');
          return '<=?';
        } else {
          is($$QM, 'reifier suffix');
          return '<?';
        }

      case $$GT:
        skip();
        if (read() === $$EQ) {
          skip();
          is($$QM, 'reifier suffix');
          return '>=?';
        } else {
          is($$QM, 'reifier suffix');
          return '>?';
        }

      case $$OR:
        skip();
        is($$QM, 'issome suffix');
        return '|?';

      case $$AND:
        skip();
        is($$QM, 'isall suffix');
        return '&?';

      case $$PLUS:
        skip();
        return '+';

      case $$DASH:
        skip();
        return '-';

      case $$STAR:
        skip();
        return '*';

      case $$DIV:
        skip();
        return '/';

      default:
        return '';
    }
  }

  function parseUexpr() {
    // it's not very efficient (we could parse an ident before and check that result here) but it'll work for now

    let c = read();

    // distinct is legacy support, same as diff()
    if (c === $$d && readD(1) === $$i && readD(2) === $$s && readD(3) === $$t && readD(4) === $$i && readD(5) === $$n && readD(6) === $$c && readD(7) === $$t && readD(8) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_DIFF, 9);
      return true;
    }
    if (c === $$d && readD(1) === $$i && readD(2) === $$f && readD(3) === $$f && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_DIFF, 5);
      return true;
    }

    if (c === $$a && readD(1) === $$l && readD(2) === $$l && readD(3) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_ALL, 4);
      return true;
    }

    if (c === $$n && readD(1) === $$a && readD(2) === $$l && readD(3) === $$l && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_NALL, 5);
      return true;
    }

    if (c === $$s && readD(1) === $$a && readD(2) === $$m && readD(3) === $$e && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_SAME, 5);
      return true;
    }

    if (c === $$s && readD(1) === $$o && readD(2) === $$m && readD(3) === $$e && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_SOME, 5);
      return true;
    }

    if (c === $$n && readD(1) === $$o && readD(2) === $$n && readD(3) === $$e && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_NONE, 5);
      return true;
    }

    if (c === $$x && readD(1) === $$n && readD(2) === $$o && readD(3) === $$r && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_XNOR, 5);
      return true;
    }

    return false;
  }

  function parseCalledListConstraint(opcode, delta) {
    dslPointer += delta;
    skipWhitespaces();
    let vals = parseVexpList();
    ASSERT(vals.length <= 255, 'dont do lists with more than 255 vars :(');
    startConstraint(opcode);
    encode16bit(vals.length);
    vals.forEach(encode16bit);
    skipWhitespaces();
    is($$RIGHTPAREN, 'parseCalledListConstraint call closer');
    expectEol();
  }

  function parseVexpList() {
    let list = [];
    skipWhitespaces();
    while (!isEof() && read() !== $$RIGHTPAREN) {
      let index = parseVexpr();
      list.push(index);

      skipWhitespaces();
      if (read() === $$COMMA) {
        skip();
        skipWhitespaces();
      }
    }

    if (!list.length) THROW('Expecting at least one expression in the list');
    return list;
  }

  function parseVexpr(resultIndex, canBeUnknown) {
    // valcall, ident, number, group
    // ALWAYS return a var or constant INDEX!

    // resultIndex is only passed on if this was an explicit
    // assignment (like the index of `X` in `X = sum(A B C)`)

    let c = read();
    let index;
    if (c === $$LEFTPAREN) {
      index = parseGrouping();
    } else if (c === $$LEFTBRACK) {
      let domain = parseDomain();
      index = addVar(undefined, domain, false, false, true);
    } else if (c >= $$0 && c <= $$9) {
      let num = parseNumber();
      index = addVar(undefined, num, false, false, true);
    } else {
      let ident = parseIdentifier();

      if (read() === $$LEFTPAREN) {
        if (ident === 'sum') index = parseArgs(ML_SUM, resultIndex, false);
        else if (ident === 'product') index = parseArgs(ML_PRODUCT, resultIndex, false);
        else if (ident === 'all?') index = parseArgs(ML_ISALL, resultIndex, true);
        else if (ident === 'diff?') index = parseArgs(ML_ISDIFF, resultIndex, true);
        else if (ident === 'nall?') index = parseArgs(ML_ISNALL, resultIndex, true);
        else if (ident === 'none?') index = parseArgs(ML_ISNONE, resultIndex, true);
        else if (ident === 'same?') index = parseArgs(ML_ISSAME, resultIndex, true);
        else if (ident === 'some?') index = parseArgs(ML_ISSOME, resultIndex, true);
        else THROW('Unknown reifier constraint func: ' + ident);
      } else {
        // implicitly declare unknown vars as [SUB,SUP]
        index = name2index(ident, false, true);
        if (index < 0) {
          if (canBeUnknown) lastUnknownIndex = index = addVar(ident, undefined, false, false, true);
          else THROW('CONSTRAINT_VARS_SHOULD_BE_DECLARED; Unknown var [' + ident + ']');
        }
      }
    }

    TRACE('parseVexpr resulted in index:', index);

    return index;
  }

  function parseGrouping() {
    is($$LEFTPAREN, 'group open');
    skipWhitespaces();
    let indexA = parseVexpr();
    skipWhitespaces();

    // just wrapping a vexpr is okay, otherwise it needs a rop
    if (read() !== $$RIGHTPAREN) {
      let rop = parseRop();
      if (!rop) THROW('Expecting right paren or rop');
      skipWhitespaces();
      let indexB = parseVexpr();
      let indexC = addVar(undefined, rop[rop.length - 1] === '?' ? [0, 1] : undefined, false, false, true);
      indexA = compileValueConstraint(indexA, rop, indexB, indexC);
      skipWhitespaces();
    }
    is($$RIGHTPAREN, 'group closer');
    return indexA;
  }

  function parseNumber() {
    let numstr = parseNumstr();
    if (!numstr) {
      THROW('Expecting to parse a number but did not find any digits c=[ord(' + read() + ')=' + String.fromCharCode(read()) + ']');
    }
    return parseInt(numstr, 10);
  }

  function parseArgs(op, resultIndex, defaultBoolResult) {
    is($$LEFTPAREN, 'args call opener');
    skipWhitespaces();
    let refs = parseVexpList();

    // note: the var may not declared if the constraint was anonymously grouped (ie `(sum(A B)>10)`)
    if (resultIndex === undefined) resultIndex = addVar(undefined, defaultBoolResult ? [0, 1] : undefined, false, false, true);
    else if (resultIndex === lastAssignmentIndex && resultIndex === lastUnknownIndex && defaultBoolResult) setDomain(resultIndex, domain_createRange(0, 1));

    TRACE('parseArgs refs:', resultIndex, ' = all(', refs, '), defaultBoolResult:', defaultBoolResult);

    startConstraint(op);
    encode16bit(refs.length); // count
    refs.sort((a, b) => a - b);
    refs.forEach(encode16bit);
    encode16bit(resultIndex);

    skipWhitespaces();
    is($$RIGHTPAREN, 'args closer');
    return resultIndex;
  }

  function parseNumstr() {
    let numstr = '';
    while (!isEof()) {
      let c = read();
      if (c < $$0 || c > $$9) break;
      numstr += String.fromCharCode(c);
      skip();
    }
    return numstr;
  }

  function parseNumList() {
    let nums = [];

    skipWhitespaces();
    let numstr = parseNumstr();
    while (numstr) {
      nums.push(parseInt(numstr, 10));
      skipWhitespaces();
      if (read() === $$COMMA) {
        ++dslPointer;
        skipWhitespaces();
      }
      numstr = parseNumstr();
    }

    if (!nums.length) THROW('Expected to parse a list of at least some numbers but found none');
    return nums;
  }

  function parseIdentsTo(target) {
    let idents = parseIdents(target);
    if (!idents.length) THROW('Expected to parse a list of at least some identifiers but found none');
    return idents;
  }

  function parseIdents(target) {
    let idents = [];

    skipWhitespaces();
    while (!isEof()) {
      let c = read();
      if (c === target) return idents;
      if (isLineEnd(c)) break;

      if (c === $$COMMA) {
        if (!idents.length) THROW('Leading comma not supported');
        skip();
        skipWhitespaces();
        if (atEol(read())) THROW('Trailing comma not supported'); // mmmm or should we? dont believe it to be relevant for this language
        c = read();
        if (c === $$COMMA) THROW('Double comma not supported');
      }

      let ident = parseIdentifier();
      idents.push(ident);

      skipWhitespaces();
    }

    if (target === undefined) return idents;
    THROW('Missing target char at eol/eof');
  }

  function readLineRest() {
    let str = '';
    while (!isEof()) {
      let c = read();
      if (isNewlineChar(c)) break;
      str += String.fromCharCode(c);
      skip();
    }
    return str;
  }

  function parseAtRule() {
    is($$AT);
    // mostly temporary hacks while the dsl stabilizes...

    let ruleName = parseIdentifier();

    if (ruleName === 'custom') {
      skipWhitespaces();
      let ident = parseIdentifier();
      skipWhitespaces();
      if (read() === $$EQ) {
        skip();
        skipWhitespaces();
      }
      switch (ident) {
        case 'var-strat':
          parseVarStrat();
          break;
        case 'val-strat':
          parseValStrat();
          break;
        case 'set-valdist':
          skipWhitespaces();
          let target = parseIdentifier();
          let config = parseRestCustom();
          setValDist(name2index(target, true), JSON.parse(config));
          break;
        case 'noleaf': {
          skipWhitespaces();

          let idents = parseIdentsTo(undefined);
          for (let i = 0, len = idents.length; i < len; ++i) {
            // debug vars are never considered leaf vars until we change that (to something else and update this to something that still does the same thing)
            // this is for testing as a simple tool to prevent many trivial optimizations to kick in. it's not flawless.

            // encode 3x to artificially inflate the count beyond most tricks
            // these should not be deduped... but keep in mind that a noleafed alias gets double the counts
            let index = name2index(idents[i]);
            for (let j = 0; j < 3; ++j) {
              encode8bit(ML_NOLEAF);
              encode16bit(index);
            }
          }
          break;
        }
        case 'nobool': {
          // debugging tool; bounty should consider this var a non-booly regardless of whether it actually is
          skipWhitespaces();

          let idents = parseIdentsTo(undefined);
          for (let i = 0, len = idents.length; i < len; ++i) {
            let index = name2index(idents[i]);
            encode8bit(ML_NOBOOL);
            encode16bit(index);
          }
          break;
        }
        case 'free':
          skipWhitespaces();
          let size = parseNumber();
          TRACE('Found a jump of', size);
          freeDirective = size;
          break;

        case 'targets':
          parseTargets();
          break;

        default:
          THROW('Unsupported custom rule: ' + ident);
      }
    } else {
      THROW('Unknown atrule [' + ruleName + ']');
    }
    expectEol();
  }

  function setValDist(varIndex, dist) {
    ASSERT(typeof varIndex === 'number', 'expecting var indexes');
    ASSERT(problem.valdist[varIndex] === undefined, 'not expecting valdists to be set twice for the same var');
    problem.valdist[varIndex] = dist;
  }

  function compileJump(size) {
    TRACE('compileJump(' + size + '), mlPointer=', mlPointer);
    ASSERT(size > 0, 'dont call this function on size=0');
    switch (size) {
      case 0: // dead code. test code should catch these cases at call site. runtime can still just ignore it.
        break; // ignore. only expliclty illustrates no free space
      case 1:
        encode8bit(ML_NOOP);
        break;
      case 2:
        encode8bit(ML_NOOP2);
        encode8bit(0);
        break;
      case 3:
        encode8bit(ML_NOOP3);
        encode8bit(0);
        encode8bit(0);
        break;
      case 4:
        encode8bit(ML_NOOP4);
        encode8bit(0);
        encode8bit(0);
        encode8bit(0);
        break;
      default:
        // because we manually update mlPointer the buffer may not grow accordingly. so do that immediately
        // but only if necessary
        const jumpDestination = mlPointer + size;
        if (mlBufSize <= jumpDestination) {
          const sizeDifference = jumpDestination - mlBufSize;
          const growAmount = (jumpDestination / 10) | 0 + sizeDifference;
          grow(growAmount);
        }

        if (size < 0xffff) {
          encode8bit(ML_JMP);
          encode16bit(size - SIZEOF_V);
          mlPointer += size - SIZEOF_V;
        } else {
          encode8bit(ML_JMP32);
          encode32bit(size - SIZEOF_W);
          mlPointer += size - SIZEOF_W;
        }
        // buffer is explicitly fill(0)'d so no need to clear it out here (otherwise we probably should)
    }
  }

  function parseVarStrat() {
    // @custom var-strat [fallback] [=] naive
    // @custom var-strat [fallback] [=] size
    // @custom var-strat [fallback] [=] min
    // @custom var-strat [fallback] [=] max
    // @custom var-strat [fallback] [=] throw
    // @custom var-strat [fallback] [inverted] [list] (a b c)

    let fallback = false; // list only
    let inverted = false; // list only
    let issed = false; // had equal sign (illegal for list)

    if (read() === $$f) {
      let ident = parseIdentifier();
      if (ident !== 'fallback') THROW('Expecting var strat name, found [' + ident + ']');
      fallback = true;
      skipWhitespaces();
    }
    if (read() === $$i) {
      let ident = parseIdentifier();
      if (ident !== 'inverted') THROW('Expecting var strat name, found [' + ident + ']');
      inverted = true;
      skipWhitespaces();
    }
    if (read() === $$EQ) {
      skip();
      issed = true;
      skipWhitespaces();
    }

    if (read() === $$LEFTPAREN) {
      parseVarStratList(fallback, inverted);
    } else {
      let ident = parseIdentifier();

      if (ident === 'naive' || ident === 'size' || ident === 'min' || ident === 'max' || ident === 'throw') {
        if (inverted) THROW('The `inverted` keyword is only used with a list');
        if (fallback) {
          addFallbackToVarStrat(ident);
        } else {
          problem.input.varstrat = ident;
        }
      } else if (ident === 'list') {
        skipWhitespaces();
        if (issed) THROW('The `=` should not be used for a list');
        if (read() !== $$LEFTPAREN) THROW('Expecting list of idents now');
        parseVarStratList(fallback, inverted);
      } else {
        THROW('Unknown var strat [' + ident + ']');
      }
    }
    skipWhitespaces();
  }
  function parseVarStratList(fallback, inverted) {
    is($$LEFTPAREN, 'List open');
    skipWhitespaces();
    let idents = parseIdents($$RIGHTPAREN);
    skipWhitespaces();
    is($$RIGHTPAREN, 'List must be closed');

    let strat = {type: 'list', inverted, priorityByName: idents};
    if (fallback) {
      addFallbackToVarStrat(strat);
    } else {
      problem.input.varstrat = strat;
    }
  }

  function addFallbackToVarStrat(strat) {
    let vs = problem.input.varstrat;
    ASSERT(vs, 'should set the var strat before declaring its backup'); // should we just throw for this?
    if (typeof vs === 'string') vs = problem.input.varstrat = {type: vs};

    while (vs.fallback) {
      if (typeof vs.fallback === 'string') {
        vs = vs.fallback = {type: vs.fallback};
      } else {
        vs = vs.fallback;
      }
    }
    vs.fallback = strat;
  }

  function parseValStrat() {
    problem.input.valstrat = parseIdentifier();
  }

  function parseRestCustom() {
    skipWhitespaces();
    if (read() === $$EQ) {
      skip();
      skipWhitespaces();
    }

    return readLineRest();
  }

  function parseTargets() {
    skipWhitespaces();
    if (read() === $$EQ) THROW('Unexpected double eq sign');

    if (read() === $$a && readD(1) === $$l && readD(2) === $$l) {
      dslPointer += 3;
    } else {
      is($$LEFTPAREN, 'ONLY_USE_WITH_SOME_TARGET_VARS; The @targets left-paren');
      let list = parseIdentsTo($$RIGHTPAREN);
      problem.freezeTargets(list);
      is($$RIGHTPAREN, 'The @targets right-paren');
    }

    expectEol();
  }

  function THROW(msg) {
    if (_debug) {
      TRACE(String.fromCharCode(...dslBuf.slice(0, dslPointer)) + '##|PARSER_IS_HERE[' + msg + ']|##' + String.fromCharCode(...dslBuf.slice(dslPointer)));
    }
    msg += ', source at ' + dslPointer + ' #|#: `' + String.fromCharCode(...dslBuf.slice(Math.max(0, dslPointer - 20), dslPointer)) + '#|#' + String.fromCharCode(...dslBuf.slice(dslPointer, Math.min(dslBuf.length, dslPointer + 20))) + '`';
    throw new Error(msg);
  }
}

function ArrayBufferTransferPoly(source, length) {
  // c/p https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/ArrayBuffer/transfer

  if (!(source instanceof ArrayBuffer))
    throw new TypeError('Source must be an instance of ArrayBuffer');
  if (length <= source.byteLength)
    return source.slice(0, length);
  const sourceView = new Uint8Array(source),
    destView = new Uint8Array(new ArrayBuffer(length));
  destView.set(sourceView);
  return destView.buffer;
}

// BODY_STOP

export {
  dsl2ml,
};
