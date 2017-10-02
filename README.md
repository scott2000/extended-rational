This crate provides implementations of high-accuracy projectively-extended
rational numbers and macros for creating them.

# Differences

Projectively-extended rationals differ from normal rationals because they have
a single, signless infinity and a single, signless zero. This means that `1/0`
can be defined as equal to `∞` and `1/∞` equal to `0`.