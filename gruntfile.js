module.exports = function () {
  var grunt = this;

  grunt.initConfig({
    babel: {
      options: { // http://babeljs.io/docs/usage/options/
        // set from package.json (this way it's global, not just this grunt task)
      },
      build: {
        files: [
          {
            expand: true,
            cwd: 'src/',
            src: ['**/*.js'],
            dest: 'build/src/',
          },
          {
            expand: true,
            cwd: 'tests/specs/',
            src: ['**/*.js'],
            dest: 'build/specs/',
          },
        ],
      },
      concat: {
        files: {
          'build/fdp-es5.js': ['build/fdp.es6.concat.js'],
        },
      },
    },

    concat: {
      build: { // "dist", prod build
        options: {
          // https://github.com/gruntjs/grunt-contrib-concat
          banner: 'let FDP = (function(){',
          footer: '\n  return FDP;\n})();\nexport default FDP;\n',
          sourceMap: true,
          sourceMapStyle: 'inline', // embed link inline
          process: function(code, path){
            if (path === 'src/index.js') return '';
            console.log('concatting', path);
            if (code.match(/console\./)) throw new Error('Found occurrence of `console.`. Do not use console directly, fetch a term through getTerm in helpers instead (also don\'t use `console.` in comments because this is a simple regex match)');
            code = removeHeaderFooter(code, path);
            code = removeAsserts(code);
            code = removeDists(code);

            return concatFile(code, path);
          },
        },
        files: {
          'build/fdp.es6.concat.js': [
            '../fdlib/src/**/*',
            'src/**/*',
          ],
        },
      },
      test: { // "bug"; keep asserts and traces etc
        options: {
          // https://github.com/gruntjs/grunt-contrib-concat
          banner: '',
          footer: '\nexport default FDP;',
          sourceMap: true,
          sourceMapStyle: 'inline', // embed link inline
          process: function(code, path){
            if (path === 'src/index.js') return '';
            console.log('concatting', path);
            if (code.match(/console\./)) throw new Error('Found occurrence of `console.`. Do not use console directly, fetch a term through getTerm in helpers instead (also don\'t use `console.` in comments because this is a simple regex match)');
            code = removeHeaderFooter(code, path);

            return concatFile(code, path);
          },
        },
        files: {
          'build/fdp.es6.concat.js': [
            '../fdlib/src/**/*',
            'src/**/*',
          ],
        },
      },
    },

    mochaTest: {
      all: {
        src: [
          'tests/specs/**/*.spec.js',
          '../fdh/tests/specs/**/*.spec.js',
        ],
        options: {
          bail: true,
          require: [
            'babel-core/register',         // translate es6 syntax to es5
            'babel-polyfill',              // babel only translates, doesnt add new libs
            './tests/specs/setup.js',      // sets the verifier up to use FDO
          ],
          // it appears that babel supports an option to redirect the rc but no idea here
          // for now it uses a default config inlined into package.json
          //babelrc: 'config/babelrc',
          timeout: 6000,
          reporter: 'spec',
          recursive: true,
        },
      },
      nobail: {
        src: [
          'tests/specs/**/*.spec.js',
          '../fdh/tests/specs/**/*.spec.js',
        ],
        options: {
          require: [
            'babel-core/register',         // translate es6 syntax to es5
            'babel-polyfill',              // babel only translates, doesnt add new libs
            './tests/specs/setup.js',      // sets the verifier up to use FDO
          ],
          // it appears that babel supports an option to redirect the rc but no idea here
          // for now it uses a default config inlined into package.json
          //babelrc: 'config/babelrc',
          timeout: 6000,
          reporter: 'spec',
        },
      },
    },

    remove: {
      default_options: {
        trace: true,
        dirList: [
          'build',
          'dist',
        ],
      },
    },

    // this is so backwards
    run: {
      coverage: {
        cmd: 'npm',
        args: ['run','coverage','--silent'],
      },
      lint: {
        cmd: 'npm',
        args: ['run','lint','--silent'],
      },
      lintdev: { // allows console/debugger
        cmd: 'npm',
        args: ['run','lintdev','--silent'],
      },
      jsbeautify: {
        cmd: 'node_modules/.bin/js-beautify',
        args: [
          '-s 4',
          '-f', 'build/fdp-es5.js',
          '-o', 'build/fdp-es5-beautified.js',
        ],
      },
    },

    uglify: {
      dist: {
        options: {
          report: 'gzip', // false, 'none', 'min', 'gzip'. gzip is a little slower but not significant and good to see.
          sourceMap: true,
          verbose: true,
        },
        files: {
          'dist/fdp.dist.min.js': ['build/fdp-es5.js'],
        },
      },
    },

    watch: {
      p: { // build for perf in browser
        files: [
          'src/**/*.js',
        ],
        tasks: [
          'distperf',
        ],
      },
      q: { // quick dist, no linting, testing, or minifying. mostly for debugging quickly.
        files: [
          'src/**/*.js',
        ],
        tasks: [
          'distq',
        ],
      },
      b: { // quick dist WITH asserts, no linting, testing, or minifying. mostly for debugging quickly.
        files: [
          'src/**/*.js',
        ],
        tasks: [
          'distbug',
        ],
      },
      h: { // quick dist WITHOUT asserts, no linting, testing, or minifying. mostly for debugging quickly.
        files: [
          'src/**/*.js',
        ],
        tasks: [
          'distheat',
        ],
      },
      t: { // run tests when anything changes
        files: [
          'src/**/*.js',
          'tests/**/*.js',
          '../fdlib/src/**/*.js',        // shared sources
          '../fdlib/tests/**/*.js',      // shared testing stuff
          '../fdh/tests/**/*.spec.js',   // actual tests
          '../fdo/src/**/*.js',          // solver
          '../fdv/**/*.js',              // verifier
        ],
        tasks: [
          'testq',
        ],
      },
      tb: { // run tests when anything changes
        files: [
          'src/**/*.js',
          'tests/**/*.js',
          '../fdlib/src/**/*.js',        // shared sources
          '../fdlib/tests/**/*.js',      // shared testing stuff
          '../fdh/tests/**/*.spec.js',   // actual tests
          '../fdo/src/**/*.js',          // solver
          '../fdv/**/*.js',              // verifier
        ],
        tasks: [
          'testtb',
        ],
      },
    },
  });

  function removeHeaderFooter(code, path) {
    var match = code.match(/^[\s\S]*?BODY_START([\s\S]*?)\/\/ BODY_STOP/);
    if (!match) {
      console.error('unable to find body start/stop pragmas in ' + path);
      throw 'No body found in ' + path;
    }
    return match[1];
  }
  function removeAsserts(code) {
    code = code.replace(/^\s*\/\/\s*__REMOVE_BELOW_FOR_ASSERTS__[\s\S]*?__REMOVE_ABOVE_FOR_ASSERTS__[\s\S]*?$/gm, function(match) {
      console.log(' - removing ' + match.length + 'b/'+code.length+'b for asserts');
      return '';
    });
    var len = code.length;
    code = code.replace(/^\s*ASSERT.*$/gm, '');
    if (code.length-len) console.log(' - removed', len-code.length, 'bytes of asserts');
    len = code.length;
    code = code.replace(/^\s*TRACE.*$/gm, '');
    if (code.length-len) console.log(' - removed', len-code.length, 'bytes of traces');
    return code;
  }
  function removeDists(code) {
    code = code.replace(/^\s*\/\/\s*__REMOVE_BELOW_FOR_DIST__[\s\S]*?__REMOVE_ABOVE_FOR_DIST__[\s\S]*?$/gm, function(match, before, after) {
      console.log(' - removing ' + match.length + 'b/' + code.length + 'b for dist');
      return '';
    });
    return code;
  }
  function concatFile(code, path) {
    return '' +
      '\n// from: ' + path + '\n\n' +
      code + '\n\n' +
      '// end of ' + path + '\n' +
      '';
  }

  grunt.loadNpmTasks('grunt-babel'); // we dont really need this but can be handy for debugging
  grunt.loadNpmTasks('grunt-contrib-uglify');
  grunt.loadNpmTasks('grunt-contrib-watch');
  grunt.loadNpmTasks('grunt-mocha-test');
  grunt.loadNpmTasks('grunt-run'); // runs npm scripts
  grunt.loadNpmTasks('grunt-remove');
  grunt.loadNpmTasks('grunt-replace');
  grunt.loadNpmTasks('grunt-contrib-concat');

  grunt.registerTask('concat-dist-to-browserjs', function() {
    console.log('- Copying dist to browser.js');
    grunt.file.copy('dist/fdp.dist.min.js', 'dist/browser.js');
  });
  grunt.registerTask('concat-bug-to-browserjs', function() {
    console.log('- Copying build to browser.js');
    grunt.file.copy('build/fdp-es5-beautified.js', 'dist/browser.js');
    grunt.file.copy('build/fdp-es5-beautified.js', 'dist/fdp.dist.min.js');
  });

  grunt.registerTask('clean', ['remove']);
  grunt.registerTask('build', 'alias for dist', ['dist']);
  grunt.registerTask('dist', 'lint, test, build, minify', ['clean', 'run:lint', 'mochaTest:all', '_dist']);
  grunt.registerTask('_dist', 'just build dist', ['clean', 'concat:build', 'babel:concat', 'uglify:dist']);
  grunt.registerTask('distq', 'create dist (inc browser.js) without testing', ['_dist', 'concat-dist-to-browserjs']);
  grunt.registerTask('distbug', 'create dist for browser debugging, keeps asserts', ['clean', 'concat:test', 'babel:concat', 'run:jsbeautify', 'concat-bug-to-browserjs']);
  grunt.registerTask('distheat', 'create dist for heatmap inspection, no asserts', ['clean', 'concat:build', 'babel:concat', 'run:jsbeautify', 'concat-bug-to-browserjs']);
  grunt.registerTask('coverage', ['clean', 'run:coverage']);
  grunt.registerTask('test', 'lint then test', ['clean', 'run:lintdev', 'mochaTest:all']);
  grunt.registerTask('testq', 'test without linting', ['clean', 'mochaTest:nobail']);
  grunt.registerTask('testtb', 'test without linting, fail fast', ['clean', 'mochaTest:all']);

  grunt.registerTask('default', ['test']);
};
