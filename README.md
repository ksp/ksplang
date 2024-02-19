<p align="center">
    <a href="https://ksp.mff.cuni.cz/h/ulohy/36/ksplang/">
    <img src="./.github/ksplang.png" width="400">
    </a>
</p>
<p align="center">
  <i align="center">A stack-based programming language with 33 instructions, independently designed
by 33 people.</i>
</p>

## Introduction
This is an implementation of [ksplang](ksplang_en.md), the best programming language (as proven by the logic of a Czech children's story).

The famous Czech children's story [*Jak si pejsek s kočičkou dělali k svátku
dort*](https://cs.wikisource.org/wiki/Pov%C3%ADd%C3%A1n%C3%AD_o_pejskovi_a_ko%C4%8Di%C4%8Dce/Jak_si_pejsek_s_ko%C4%8Di%C4%8Dkou_d%C4%9Blali_k_sv%C3%A1tku_dort)
([English translation](https://easystoriesinenglish.com/cake/)) by Josef Čapek
teaches that you can bake the best cake by adding many good things into it.
Yes, that is *definitely* the correct interpretation. We have decided to prove
this experimentally, with a programming language.

We have done this within [KSP](https://ksp.mff.cuni.cz/), a Czech programming
competition for high-school students. Within the first series of tasks of the 36th year, we have asked
each competitor for a single original instruction for a stack-based language.
The result is [ksplang](ksplang_en.md), and you are currently looking at its
reference implementation in Rust.

## The ksplang interpreter
This repository includes a `ksplang` executable which can be used to run ksplang programs.
Input is given on the standard input as whitespace-separated numbers (or [text](#text-mode)).

### Example usage
```sh
./ksplang program.ksplang < input.txt > output.txt
```

**program.ksplang** – the ksplang program:
```ksplang
pop ++
```

**input.txt** – the input stack:
```
41 12
```

**output.txt** – the result:
```
42
```

### Text mode

The interpreter can also be used in text mode, which translates input from text to numbers and output from numbers to text (as Unicode code points).
You can also do this only for input or output with `--text-input` and `--text-output`, respectively.

```sh
echo -n "aaa" | ./ksplang -t program.ksplang
# prints "ab"
```

### More options
- `--stats` (`-s`) - print statistics on stderr
- `--max-stack-size` (`-m`) - set the maximum stack size

## Building from source
1. Clone the repository: `git clone https://github.com/ksp/ksplang.git`
2. Within the `ksplang` directory, run `cargo build -p ksplang-cli --release`
3. You can now run `target/release/ksplang-cli`

## Online interpreter
An online version of the interpreter with a simple stepping debugger lives [on the KSP webpage](https://ksp.mff.cuni.cz/h/ulohy/36/ksplang/sim.html).

## Contributing
If you have improvements to the reference implementation, the tooling,
or the descriptions, feel free to create an issue or a pull request.

No changes to the language are allowed as the language is perfect.

## License
This code is available under the MIT License. See the [LICENSE](LICENSE) file for details.