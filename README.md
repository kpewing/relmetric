# relmetric
Tools for computing distances between relation matrices, based on [Kenneth P. Ewing & Michael Robinson, "Metric Comparison of Relations," p. 7](https://arxiv.org/abs/2105.01690).

Forked from https://github.com/kb1dds/relmetric.

- **BEWARE**: The *weight* might be mathematically wrong.

I added a [Lua 5.4](https://www.lua.org) version of the software (now) in a subdirectory [lua](https://github.com/kpewing/relmetric/tree/main/lua):

- includes methods for binary operations on *relations* and to estimate the *distance bound* from [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
- **BEWARE**: The *weight* might be mathematically wrong.

I added a [Rust 1.65](https://www.rust-lang.org) version of the software in its own [rust](https://github.com/kpewing/relmetric/tree/main/rust) subdirectory:

- uses corrected algorithm to calculate *weight*
- includes *distance bound* estimate, binary operations, pretty-printing, binary printing, hexadecimal printing, and for *relations* and *columns*, as well as pretty-printing the *x-group* partition of a *relation*
- **Rust**-style documentation for the entire crate with detailed examples from [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690)
