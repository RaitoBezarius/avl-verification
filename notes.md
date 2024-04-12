# Formalization notes

- Inhabited is not synthesized systematically for any type.
- Synthesize type aliases (?): requires to obtain this information before MIR.

## Bundle of specifications

Most of the time, we have naked types which does not exhibit their "expected" specification,
e.g. an `Ord` trait which does not prove that it's an order.

Ideally, we need to be able to build trait specifications and find a way to unbundle them and use them in the different tactics.

## Errors

```
avl on  avl is  v0.1.0 via  v1.73.0 via ❄️  impure (shell) 
❯ nix run github:aeneasverif/aeneas -L -- -backend lean avl_verification.llbc
[Info ] Imported: avl_verification.llbc
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1488:8-1488:47
[Error] Could not translate the function signature of 'core::cmp::impls::{(core::cmp::Ord for &0 (A))#11}::cmp' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1488:8-1488:47
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1462:8-1462:61
[Error] Could not translate the function signature of 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::partial_cmp' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1462:8-1462:61
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1466:8-1466:40
[Error] Could not translate the function signature of 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::lt' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1466:8-1466:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1470:8-1470:40
[Error] Could not translate the function signature of 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::le' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1470:8-1470:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1474:8-1474:40
[Error] Could not translate the function signature of 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::gt' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1474:8-1474:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1478:8-1478:40
[Error] Could not translate the function signature of 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::ge' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1478:8-1478:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1448:8-1448:40
[Error] Could not translate the function signature of 'core::cmp::impls::{(core::cmp::PartialEq<&0 (B)> for &1 (A))#9}::eq' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1448:8-1448:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1452:8-1452:40
[Error] Could not translate the function signature of 'core::cmp::impls::{(core::cmp::PartialEq<&0 (B)> for &1 (A))#9}::ne' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1452:8-1452:40
[Error] Internal error, please file an issue
Source: 'src/main.rs', lines 14:4-16:5
[Error] Internal error, please file an issue
Source: 'src/main.rs', lines 18:4-20:5
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 23:47-25:9
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 31:49-33:9
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 49:4-75:5
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 77:4-103:5
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 105:4-131:5
[Error] There should be no bottoms in the value
Source: 'src/main.rs', lines 148:52-154:9
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1488:8-1488:47
[Error] Could not translate the function 'core::cmp::impls::{(core::cmp::Ord for &0 (A))#11}::cmp' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1488:8-1488:47
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1462:8-1462:61
[Error] Could not translate the function 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::partial_cmp' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1462:8-1462:61
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1466:8-1466:40
[Error] Could not translate the function 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::lt' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1466:8-1466:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1470:8-1470:40
[Error] Could not translate the function 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::le' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1470:8-1470:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1474:8-1474:40
[Error] Could not translate the function 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::gt' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1474:8-1474:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1478:8-1478:40
[Error] Could not translate the function 'core::cmp::impls::{(core::cmp::PartialOrd<&0 (B)> for &1 (A))#10}::ge' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1478:8-1478:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1448:8-1448:40
[Error] Could not translate the function 'core::cmp::impls::{(core::cmp::PartialEq<&0 (B)> for &1 (A))#9}::eq' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1448:8-1448:40
[Error] Nested borrows are not supported yet
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1452:8-1452:40
[Error] Could not translate the function 'core::cmp::impls::{(core::cmp::PartialEq<&0 (B)> for &1 (A))#9}::ne' because of previous error
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1452:8-1452:40
[Error] Overriding trait provided methods in trait implementations is not supported yet (overriden methods: lt, le, gt, ge)
Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/core/src/cmp.rs', lines 1457:4-1457:52
```

Checkpoint 2:
```
avl on  avl is  v0.1.0 via  v1.73.0 via ❄️  impure (shell) 
❯ nix run github:aeneasverif/aeneas -L -- -backend lean avl_verification.llbc
[Info ] Imported: avl_verification.llbc
[Info ] Generated the partial file (because of errors): ./AvlVerification.lean
[Error] Internal error, please file an issue
Source: 'src/main.rs', lines 41:4-43:5
[Error] Internal error, please file an issue
Source: 'src/main.rs', lines 45:4-47:5
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 50:47-52:9
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 58:49-60:9
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 76:4-102:5
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 104:4-130:5
[Error] ADTs containing borrows are not supported yet
Source: 'src/main.rs', lines 132:4-158:5
[Error] There should be no bottoms in the value
Source: 'src/main.rs', lines 175:52-181:9
```
