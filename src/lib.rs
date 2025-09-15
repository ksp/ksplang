//! # ksplang
//! A stack-based programming language with 33 instructions, independently designed
//! by 33 people.
//! ## Introduction
//! This is an implementation of ksplang, the best programming language, as proven by
//! the logic of a Czech children's story.
//!
//! The famous Czech children's story [*Jak si pejsek s kočičkou dělali k svátku
//! dort*](https://cs.wikisource.org/wiki/Pov%C3%ADd%C3%A1n%C3%AD_o_pejskovi_a_ko%C4%8Di%C4%8Dce/Jak_si_pejsek_s_ko%C4%8Di%C4%8Dkou_d%C4%9Blali_k_sv%C3%A1tku_dort)
//! ([English translation](https://easystoriesinenglish.com/cake/)) by Josef Čapek
//! teaches that you can bake the best cake by adding many good things into it.
//! Yes, that is *definitely* the correct interpretation. We have decided to prove
//! this experimentally, with a programming language.
//!
//! We have done this within [KSP](https://ksp.mff.cuni.cz/), a Czech programming
//! competition for high-school students. Within the first series of tasks of the 36th year,
//! we have asked each competitor for a single original instruction for a stack-based language.
//! The result is *ksplang*, and you are currently looking at its
//! reference implementation in Rust.
pub mod ops;
pub mod parser;
pub mod vm;
pub mod funkcia;
