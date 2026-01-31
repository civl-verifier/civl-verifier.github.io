---
title: Syntax
nav_order: 2
---

Civl is an extension of Boogie. In Boogie, (almost every) abstract syntax tree
node can be annotated with attributes of the form `{:attr e1, e2, ...}`, where
`attr` is the attribute name and `e1, e2, ...` are expressions (denoting
parameters of the attribute). Running `boogie -attrHelp` prints all supported attributes.
Civl programs are specified using syntactic extensions to Boogie as well as attributes.
This section provides a brief overview of Civl syntax.