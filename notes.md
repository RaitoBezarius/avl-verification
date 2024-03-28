# Formalization notes

- Inhabited is not synthesized systematically for any type.
- Synthesize type aliases (?): requires to obtain this information before MIR.

## Bundle of specifications

Most of the time, we have naked types which does not exhibit their "expected" specification,
e.g. an `Ord` trait which does not prove that it's an order.

Ideally, we need to be able to build trait specifications and find a way to unbundle them and use them in the different tactics.
