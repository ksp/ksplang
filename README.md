<p align="center">
    <img src="./ksplangjit-logo.png" width="500">
</p>
<p align="center">
  A faster runtime for the <i align="center">stack-based programming language with 33 instructions, independently designed
by 33 people.</i>
</p>

<div align="center">

</div>

## KsplangJIT

This is a faster and less stable runtime for [ksplang](ksplang_en.md), the best programming language (as proven by the logic of a Czech children's story).

See the reference implementation for more information: [github.com/ksp/ksplang](https://github.com/ksp/ksplang).

## Usage

Add `--optimize` flag to start the interpreter with the JIT enabled.

### Example usage
```sh
./ksplang --optimize program.ksplang < input.txt > output.txt
```

All options from the reference interpreter are supported, for example `--text-input`, `--text-output`, `--stats`, `--max-stack-size`.

## JIT options

For now, the optimizer is configured using env variables.
Exhaustive list is in the ./src/compiler/config.rs source file.

* `KSPLANGJIT_VERBOSITY` = 0 (should be no logging) .. 255 (highest)
* `KSPLANGJIT_TRIGGER_COUNT` = 1 ..
  - after how many executions of an instruction consider starting compiling
  - this may have very significant impact on performance
  - try increasing the number if you hit bugs (after reporting them of course)
* `KSPLANGJIT_TRACE_LIMIT` = 0 ..
  - how long the trace should be
  - set to 0 to disable tracing and only compile statically (this might also workaround some bugs)
* `KSPLANGJIT_VERIFY`
  - 0
  - 1: after compiling, run the compiled program and the reference interpreter and compare the results
  - 2: compare the results after every single run of a compiled block
    - this finds almost all bugs, but is very slow (much slower than normal interpreter)
    - it will also try to reproduce the bug with a smaller compiled program
  - 3: same, but might be more successful with the program shrinking
* `KSPLANGJIT_ADHOC_INTERPRET_LIMIT` = 0 ..
  - limits the numbers of ksplang instructions ingested into the compilation
* `KSPLANGJIT_DUMPDIR` = /filesystem/directory/
  - dumps some data into the directory
    - it will be all compiled CFGs
    - and `stats.csv` with some stats (how many times was a given compiled CFG executed, etc)

## Building from source
1. Clone the repository: `git clone https://github.com/ksp/ksplang.git`
2. Within the `ksplang` directory, run `cargo build -p ksplang-cli --release`
3. You can now run `target/release/ksplang-cli`

## License
This code is available under the MIT License. See the [LICENSE](LICENSE) file for details.
