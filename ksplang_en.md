# ksplang - the best programming language

ksplang is a stack-based programming language with 33 instructions, independently designed
by 33 people. Proven best by the logic of a Czech children's story.

## About the language

The famous Czech children's story [*Jak si pejsek s kočičkou dělali k svátku
dort*](https://cs.wikisource.org/wiki/Pov%C3%ADd%C3%A1n%C3%AD_o_pejskovi_a_ko%C4%8Di%C4%8Dce/Jak_si_pejsek_s_ko%C4%8Di%C4%8Dkou_d%C4%9Blali_k_sv%C3%A1tku_dort)
([English translation](https://easystoriesinenglish.com/cake/)) by Josef Čapek
teaches that you can bake the best cake by adding many good things into it.
Yes, that is *definitely* the correct interpretation. We have decided to prove
this experimentally, with a programming language.

We have done this within [KSP](https://ksp.mff.cuni.cz/), a Czech programming
competition for high-school students. Within the first series of tasks of the 36th year, we have asked
each competitor for a single original instruction for a stack-based language.
Within the second and third series we have assigned tasks to solve in ksplang.

## The basics

We have one stack of limited size (configurable) of 64-bit signed values (-2^63
to 2^63-1). The initial stack is the input, the resulting stack is the
output. Overflows are generally an error, so is indexing out of bounds. The
list of instructions is indexed from zero. Instructions have ids (0 to 32).
Programs are sequences of case insensitive instructions, separated by
whitespace. No comments are allowed. The program ends when the program naturally
reaches past the end or the start when executing backwards.

## Tasks
These tasks can be a good starting point for learning the language. In all tasks, the input stack is non-empty.

- [36-2-4](https://ksp.mff.cuni.cz/viz/36-2-4), task 1: Add 0 to the stack
- [36-2-4](https://ksp.mff.cuni.cz/viz/36-2-4), task 2: Turn x into -x (except for -2^63)
- [36-2-4](https://ksp.mff.cuni.cz/viz/36-2-4), task 3: Duplicate a number
- [36-3-4](https://ksp.mff.cuni.cz/viz/36-3-4), task 1: Turn positive `k` into a sequence `k k-1 ... 0`
- [36-3-4](https://ksp.mff.cuni.cz/viz/36-3-4), task 2: Sort the stack (given its length)
- [36-3-4](https://ksp.mff.cuni.cz/viz/36-3-4), task 3: Calculate the stack length

## Overview of instructions

You can check out the original Czech instruction list
[here](https://ksp.mff.cuni.cz/viz/ksplang), but we also provide a translation
of all the instructions here.

Generally, we talk about the stack growing right or upwards.

### Stack manipulation

| ID | Zápis    | Popis                                                                                               |
|----|----------|-----------------------------------------------------------------------------------------------------|
| 0  | `praise` | Adds \"Mám rád KSP\" N times (Czech for "I like KSP").                                              |
| 1  | `pop`    | Removes the top value.                                                                              |
| 2  | `pop2`   | Removes the second value from the top.                                                              |
| 3  | `max`    | Removes the smaller of the top two values.                                                          |
| 4  | `L-swap` | Swaps the first and last value on the stack.                                                        |
| 5  | `lroll`  | Rolls the top N values on the stack K positions to the right.                                       |
| 6  | `-ff`    | If the top of the stack is 2, then 4, do nothing; otherwise empty the stack and fill it with -2^63. |
| 7  | `swap`   | Pop an index n, then swap new top value with n-th value from the bottom (zero-indexed).             |
| 8  | `kPi`    | Gets decimal digits of π (see full description for details).                                        |

### Arithmetic

| ID | Zápis      | Popis                                                                                                                                      |
|----|------------|--------------------------------------------------------------------------------------------------------------------------------------------|
| 9  | `++`       | Increments the top number by 1.                                                                                                            |
| 10 | `u`        | Universal arithmetic; first pops operation id, then does addition/absolute difference/multiplication/division or remainder/factorial/sign. |
| 11 | `REM`      | Truncated division modulo (like `a % b` in C).                                                                                             |
| 12 | `%`        | Euclidean modulo (like `a % abs(b)` in Python).                                                                                            |
| 13 | `tetr`     | Tetration.                                                                                                                                 |
| 14 | `^^`       | Tetration (reverse parameter order compared to tetr).                                                                                      |
| 15 | `m`        | Median of top k numbers, k is top value on the stack (not removed).                                                                        |
| 16 | `CS`       | Digit sum of top number (not removed).                                                                                                     |
| 17 | `lensum`   | Sum "decimal lengths" of top two numbers on the stack.                                                                                     |
| 18 | `bitshift` | Left bitshift.                                                                                                                             |
| 19 | `And`      | Bitwise AND of top two numbers.                                                                                                            |
| 20 | `sum`      | Sum the entire stack.                                                                                                                      |
| 21 | `gcd`      | GCD of two numbers.                                                                                                                        |
| 22 | `d`        | GCD of n numbers.                                                                                                                          |
| 23 | `qeq`      | Finds integer solutions of quadratic equations.                                                                                            |
| 24 | `funkcia`  | Factorizes 2 numbers and multiplies the factorization except for common primes, modulo 1000000007.                                         |
| 25 | `bulkxor`  | Pops N and then applies XOR to N pairs of values interpreted as x \> 0 and creates N zeros/ones.                                           |

### Control flow

IP is the current instruction pointer.

| ID | Zápis  | Popis                                                                                                        |
|----|--------|--------------------------------------------------------------------------------------------------------------|
| 26 | `BRZ`  | Sets IP to second top value if the top is zero (conditional absolute jump).                                  |
| 27 | `call` | Adds IP+1 to the stack and sets top of the stack as IP (absolute jump with return IP).                       |
| 28 | `GOTO` | Sets IP to top value (absolute jump).                                                                        |
| 29 | `j`    | Adds top value + 1 to IP (relative jump).                                                                    |
| 30 | `rev`  | Jumps forward, rotates the stack and executes code backwards until itself (see full description for details) |

### Other

| ID | Zápis    | Popis                                                                                                                                                             |
|----|----------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31 | `SPANEK` | During task evaluation, gives double the points and goes to sleep... (results in a timeout error)                                                                 |
| 32 | `deez`   | Reads n values, translates them to instructions by their ids, evaluates the subprogram and appends the resulting stack as instructions to the end of the program. |
