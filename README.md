# FDP - FD Preprocessor reduction system

A [Finite Domain Preprocessor](https://en.wikipedia.org/wiki/Constraint_logic_programming) [term reduction system](https://en.wikipedia.org/wiki/Rewriting), forked from [finitedomain](https://github.com/the-grid/finitedomain) where I tentatively started doing it.

This is my personal fork of the [finitedomain](https://github.com/the-grid/finitedomain) library from when I stopped working on it.

Part of the [fdq](https://github.com/qfox/fdq) package. See its description for a complete overview of this suite and how to run tests and all that.

This is very much a WIP but might not be very actively maintained.

## REPL

There's [an online playground](https://qfox.github.io/fdp/examples/playground.html) with a not-necessarily-up-to-date build where you can experiment with this package. This web version currently does not work in Edge nor Safari nor any other browser that does not support the `TextEncoder` class. The page is just a simple UI and a WIP.

The repo also contains an example [Sudoku solver](https://qfox.github.io/fdp/examples/sudoku.html), a [Battleships solver](https://qfox.github.io/fdp/examples/battleships.html), and, [Tents puzzle solver](https://qfox.github.io/fdp/examples/treetent.html). I was working on [Hitori](https://qfox.github.io/fdp/examples/hitori.html) but my approach simply takes too long to solve so that one isn't very useful.

## Installing

```
npm install fdp
```

## Usage

Find all numbers between 10 and 20 that are bigger than 14 and smaller than 17 and not 16. Contrived? Nah.

```es6
import FDP from 'fdp';

let solution = FDP.solve(`
  : A [10 20]
  A > 14
  A < 17
  A != 16
`);

console.log(solution); // -> {A: 15}
```

For the DSL syntax see the docs in [fdq](https://github.com/qfox/fdq).
For other details see the extensive test suite in [fdh](https://github.com/qfox/fdh).

## Tasks

There are a few grunt tasks and bash scripts hooked up to npm. This repo also uses git hooks for pre- and post commit hooks.

As a general rule, `./build` is used for any temporary output, including code coverage reports and temporary build files when producing a dist.

Then `./dist` only contains final builds (`./dist/fdp.dist.min.js` and for some tasks `./dist/fdp.js`).

Note that both `./build` and `./dist` are cleared at the start of almost every (grunt) task.

(These tasks obviously require an `npm install`)

### Grunt tasks:

- `grunt clean`: removes `./dist` and `./build`
- `grunt build`: a direct alias for `dist`
- `grunt dist`: lint, test, build, and minify to produce a real dist build
- `grunt distq`: create a dist but skip linting, testing, and code coverage. Also produces a copy in `./dist/fdp.js`
- `grunt distbug`: creates a build without removing test artifacts or minification. In case you need proper stack traces in other projects.
- `grunt distheat`: creates a dist but instead of minification as the last step it beautifies. Used for [HeatFiler](https://qfox.github.io/heatfiler/src/index.html), a count based heatmap profiler. Copies to `fdp.js`.
- `grunt coverage`: runs all tests in the code coverage tool
- `grunt test`: runs linting and all tests
- `grunt testq`: runs tests without linting
- `grunt testtb`: testq but fail fast
- `grunt watch:q`: runs `distq` whenever a file changes
- `grunt watch:h`: runs `distheat` whenever a file changes
- `grunt watch:b`: runs `distbug` whenever a file changes
- `grunt watch:t`: runs `testq` whenever a file changes
- `grunt watch:tb`: runs `testtb` whenever a file changes

### Bash / npm scripts:

- `npm run lint`: run eslint with dist config (slightly stricter than dev). Exits non-zero if it fails.
- `npm run lintdev`: run eslint with dev config (allows `console.log`, `debugger`, etc). No non-zero exit for failures.
- `npm run lintfix`: runs eslint in the fix mode
