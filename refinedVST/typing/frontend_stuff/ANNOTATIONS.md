RefinedC type system annotation syntax
======================================

The RefinedC type system interfaces to the C language using:
 - [C2X attributes](http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2335.pdf)
   of the form `[[rc::<ident>(<string>, ... ,<string>)]]`,
 - macros defined in [`refinedc.h`](theories/examples/inc/refinedc.h) that are
   provided as a shortcut for using certain specific attributes in the body of
   functions,
 - special comments of the form `//rc::<ident> <payload>?`.

# Contents

[[_TOC_]]

# Valid attributes

RefinedC attributes of the form `[[rc::<ident>(<string>, ... ,<string>)]]` can
be placed on certain C constructs (e.g., on functions or on loops). Attributes
of several kinds can be specified, they are distinguished using the identifier
that they carry. Each specific kind of attribute is constrained as to where it
may appear in the source code. For instance, postcondition attributes may only
appear on a function definition or a function declaration. The following table
gives information about every available kind of attributes, including how many
arguments (i.e., strings) it may have, and what syntactic constructs it can be
attached to.

| Identifier     | Arguments   | Allowed on            | Syntax for the arguments                   |
|----------------|-------------|-----------------------|--------------------------------------------|
| `annot_args`   | One or more | Functions             | `<integer> ":" <integer> <coq_expr>`       |
| `annot`        | Exactly one | Expressions           | Arbitrary Coq syntax                       |
| `args`         | One or more | Functions             | `<type_expr>`                              |
| `constraints`  | One or more | Structures, Loops     | `<constr>`                                 |
| `ensures`      | One or more | Functions             | `<constr>`                                 |
| `exists`       | One or more | Functions, Loops      | `<ident> ":" <coq_expr>`                   |
| `let`          | One or more | Structures            | `<ident> {":" <coq_expr>`} "=" <coq_expr>  |
| `field`        | Exactly one | Structure members     | `<type_expr>`                              |
| `global`       | Exactly one | Global variables      | `<type_expr>`                              |
| `immovable`    | None        | Structures            | N/A                                        |
| `inv_vars`     | One or more | Loops                 | `<ident> ":" <type_expr>`                  |
| `lemmas`       | One or more | Functions             | Argument for the Coq `apply:` tactic       |
| `manual_proof` | Exactly one | Functions             | `<import_path> ":" <ident> "," <ident>`    |
| `parameters`   | One or more | Functions, Structures | `<ident> ":" <coq_expr>`                   |
| `typedef`      | Exactly one | Structures            | `<ident> ":" <type_expr>`                  |
| `refined_by`   | One or more | Structures            | `<ident> ":" <coq_expr>`                   |
| `requires`     | One or more | Functions             | `<constr>`                                 |
| `returns`      | Exactly one | Functions             | `<type_expr>`                              |
| `size`         | Exactly one | Structures            | `<coq_expr>`                               |
| `skip`         | None        | Functions             | N/A                                        |
| `tactics`      | One or more | Functions             | Arbitrary _Ltac_ tactic                    |
| `tagged_union` | Exactly one | Structures            | `<coq_expr>`                               |
| `trust_me`     | None        | Functions             | N/A                                        |
| `union_tag`    | Exactly one | Union members         | `<ident> {"(" <ident> ":" <coq_expr> ")}*` |
| `unfold_order` | Exactly one | Structures            | `<integer>`                                |

Note that only the attributes requiring one or more arguments may be used more
than once in the annotations for a particular C construct.

**Remark:** the ordering of attributes does not matter except between those of
the same kind. Having several attributes of a repeatable kind is equivalent to
having a single one carrying all the combined arguments (in attributes order).
As an example, the annotations on the following functions are equivalent.
```c
[[rc::parameters("i : Z")]]
[[rc::args("int<i32>", "i @ int<i32>")]] // Spec for the two arguments.
[[rc::returns("i @ int<i32>")]]
int snd_0(int x, int y){
  return y;
}

[[rc::parameters("i : Z")]]
[[rc::args("int<i32>")]] // Spec for the first argument.
[[rc::args("i @ int<i32>")]] // Spec for the second argument.
[[rc::returns("i @ int<i32>")]]
int snd_1(int x, int y){
  return y;
}

[[rc::args("int<i32>")]] // Spec for the first argument.
[[rc::parameters("i : Z")]]
[[rc::args("i @ int<i32>")]] // Spec for the second argument.
[[rc::returns("i @ int<i32>")]]
int snd_2(int x, int y){
  return y;
}
```

**Remark:** attributes on functions may be placed either on its declaration or
on its definition (or a combination of both).


# Placement of attributes

As show in the above examples, annotations on functions are placed immediately
before their definitions and/or declarations. And things go similarly for most
of the annotations, including those on loops, structure or union members. Note
that in all these cases, there should be no blank line interleaved between the
annotations themselves, or between the annotations and the element of C syntax
to which they will be attached.

In fact, there is only one kind of annotation for which the annotation must be
given in a somewhat unexpected place: structures. On a structure attributes do
not precede the declaration, they are placed right after the `struct` keyword.
An example of this is given below.
```c
struct
[[rc::refined_by("r : nat", "g : nat", "b : nat")]]
color {
  [[rc::field("r @ int<u8>")]]
  uint8_t r;

  [[rc::field("g @ int<u8>")]]
  uint8_t g;

  [[rc::field("b @ int<u8>")]]
  uint8_t b;
};
```


# Description of the attributes

In the following we describe the syntax and semantics for the arguments of the
supported attributes. The syntax will be described using a BNF-like format. We
will rely on the grammar defined in the following section.

## `rc::annot_args` (for advanced users)

This annotation appears on functions only and has at least one argument. Every
argument is of the following form.
```
<integer (as argument index)> ":" <integer (as payload)> <coq_expr (as payload)>
```
It contains a first integer, corresponding to the index of an argument (of the
function), and an annotation payload built of a natural number and a Coq term.

The annotation has the effect of attaching the specified payloads to effective
arguments of the function when it is called.

## `rc::annot` (for advanced users)

This annotation appears on toplevel expressions (treated as statements) and it
must only have a single, arbitrary string argument, that is interpreted as raw
Coq code.

The annotation has the effect of attaching the given payload to the expression
it is attached to. Note that the `rc::annot` should only be use through macros
defined in [`refinedc.h`](theories/examples/inc/refinedc.h).

## `rc::args`

This annotation appears on functions only, and requires one or more arguments.
Each argument is of the following form
```
<type_expr (as argument type)>
```
and it specifies the refinement type that is associated with the corresponding
argument of the function (in order). There must be exactly as many argument of
`rc::args` annotations as there are arguments to the function.

## `rc::constraints`

This annotation may appear on structures and on loops, and it must have one or
more arguments. Each argument is of the following form
```
<constr>
```
and it specifies a constraint that should be satisfied. On a structure, such a
constraint is checked for all expressions of the corresponding structure type.
On a loop, a constraint is part of the loop invariant and it must hold through
the whole loop.

## `rc::ensures`

This annotation appears on functions only, and requires one or more arguments.
Each argument is of the following form
```
<constr (as post-condition)>
```
and it specifies a post-condition (i.e., the constraint should hold after that
the function has returned).

## `rc::exists`

This annotation may appear on functions, loops and structs. It should carry at least
one argument, and its arguments should all be of the following form.
```
<ident (as variable name)> ":" <coq_expr (as Coq type)>
```
It corresponds to an existentially quantified variable with the given type. On
a function, this variable can only appear in post-conditions and on the return
type of the function (see `rc::ensures` and `rc::returns`). On the other hand,
when used on a loop, the variable is bound in the whole invariant.

## `rc::let`

This annotation may appear on structures and should have at least one argument
of the following form.
```
<ident (as variable name)> {":" <coq_expr (as Coq type)>} "=" <coq_expr>
```
It corresponds to a Coq let-binding with an optional type annotation. All such
bindings are inserted in the type definition under the existentials (specified
with `rc::exists`).

## `rc::field`

This annotation only appears on structure members, and it requires exactly one
argument of the following form.
```
<type_expr (as field type)>
```
and it specifies the refinement type that corresponds to the structure member.
Note that a `rc::field` annotation must be given for all structure fields that
are involved in the definition of a refinement type.

## `rc::global`

This annotation appears only on global variable declarations, and it must have
a single argument of the following form.
```
<type_expr (as global variable type)>
```
It gives the refinement type corresponding to the global variable.

## `rc::immovable`

This annotation appears only on structures, and it does not expect arguments.
It makes the type as immovable, which prevents the generation of unfolding
lemmas for value type assignments.

## `rc::inv_vars`

This annotation appears only on loops, and it carry one or more arguments. The
arguments should all be of the following form.
```
<ident (as C local variable name)> ":" <type_expr (as the variable type)>
```
Here, the identifier should correspond to a local C variable (arguments of the
current function are included), and the annotation specifies the corresponding
refinement type for the variable during the loop.

**Remark:** if a C function argument is not specified then it is automatically
annotated with its type in the function specification (see `rc::args`). On the
other hand, this behaviour is overridden when a specific type is specified.

## `rc::lemmas`

This annotation appears on functions exclusively, and it must have one or more
arguments. Every argument is expected to be a valid parameter for the `apply:`
Coq tactic, but the syntax is otherwise arbitrary. In general, this annotation
can be used to specified lemmas that RefinedC's automation will try to use (to
solve accumulated side-conditions).

## `rc::manual_proof`

This annotation appears on functions only, and requires a single argument. The
argument should be of the following form.
```
<import_path> ":" <ident (as module name)> "," <ident (as theorem name)>
```
This annotation instructs the system that the function will be proved manually
by the user. The argument gives the name of the user-written typing lemma (the
last identifier), together with the qualification path and name for the module
where it is defined.

For example, `[[rc::manual_proof("x.y : z, thm")]]` will lead to the following
Coq import to bring theorem `thm` in scope: `From x.y Require Import z.`.

## `rc::parameters`

This annotation can appear either on functions and on structures. It should be
given at least one argument of the following form.
```
<ident (as variable name)> ":" <coq_expr (as Coq type)>
```
It corresponds to an universally quantified variable with the given type. When
on a function, such a variable is bound in the whole specification. Similarly,
on structures such variables are bound in the refinement type corresponding to
the structure. (A refinement type is generated for all annotated structures.)

## `rc::typedef`

This annotation only appears on structures, and it expects one argument of the
following form.
```
<ident (as pointer type name)> : <type_expr (as type wrapper containing an ellipsis)>
```
The identifier should correspond to the name defined (using a `typedef`) for a
pointer to a structure in the C code. When given, this annotation instructs the
system to generate a refinement type corresponding to the pointer type instead
of the structure directly. The type expression specified inside the annotation
should contain an ellipsis (i.e., a type expression of the form `...`), in the
place where the type that would have been generated of the structure is put in
the generated type.

## `rc::refined_by`

This annotation appears on structures exclusively, and it must be given one or
more arguments of the following form.
```
<ident (as variable name)> : <coq_expr (as Coq type)>
```
When annotations are provided on a structure,  a corresponding refinement type
is automatically generated. The idea is that an element of the structure has a
refinement formed of (a tuple of) mathematical (i.e., Coq) values. Each of the
arguments of the `rc::refined_by` annotation specify such a value, with a name
and a type. The name is bound in constraints as also in field annotations (see
`rc::field`) on the structure (and on nested structures).

## `rc::requires`

This annotation appears on functions only, and requires one or more arguments.
Each argument is of the following form
```
<constr (as pre-condition)>
```
and it specifies a pre-condition (i.e., the constraint should hold at the call
sites of the function).

## `rc::returns`

This annotation appears on functions only,  and it should be given exactly one
argument of the following form.
```
<type_expr (as return type)>
```
The argument specifies the refinement type corresponding to the value returned
by the function.

## `rc::size`

This annotation appears on structures exclusively, and it should carry exactly
one argument of the following form.
```
<coq_expr (as RefinedC layout)>
```
The given Coq expression should correspond to a RefinedC layout. If `rc::size`
is given on a structure, the produced type is considered to be padded so as to
occupy the same space as the specified layout.

## `rc::skip`

This annotation can only appear on functions, and it expects no argument. When
given, no specification nor proof script is generated for the function.

**Remark:** This is the default behaviour when a function has no annotation.

## `rc::tactics`

This annotation appears on functions only, and requires one or more arguments.
Each argument is expected to be valid _LTac_ that is inlined at the end of the
proof script for the function (to prove remaining side-conditions).

## `rc::tagged_union`

This annotation appears on structures exclusively, and it should carry exactly
one argument of the following form.
```
<coq_expr (as Coq inductive type)>
```
When given, this annotation marks the structure as representing a tagged union
refined by a Coq expression of the specified inductive type.

## `rc::trust_me`

This annotation can only appear on functions, and it expects no argument. When
given, no proof script is generated for the function and the system trusts the
user that the function adheres to its specification.

## `rc::union_tag`

This annotation appears on union members only, and it should carry exactly one
argument of the following form.
```
<ident (as variant name)> {"(" <ident (as variable name)> ":" <coq_expr (as Coq type)> ")}*
```
The identifier gives the name of the Coq variant that will refine the  current
union member. Note that the annotation should also contain the type of all the
arguments of the variant, together with a name. This name can be used to refer
to the corresponding parameter in annotations on nested structures.

## `rc::unfold_order`

This annotation appears only on structures, and should carry exactly one integer
argument. This integers specifies in which order this type should be unfolded
relative to other types. Lower numbers are unfolded first and the default is 100.


# Grammar for annotations

The annotations described above rely on a custom syntax providing classes like
constraints or type expressions (i.e., `<constr>` or `<type_expr>`). These new
syntactic constructs will be presented here along with their semantics.

## Basic tokens

Our syntax makes use of the following regular expressions.

```
<ident>   ::= Regexp([A-Za-z_][A-Za-z_0-9]+) | "void*"
<ty_name> ::= Regexp(&?[A-Za-z_][A-Za-z_0-9]+)
<integer> ::= Regexp([0-9]+)
```
They range over general-purpose identifiers (for `<ident>`), over "type names"
(for `<ty_name>`), and over positive integer respectively (for `<integer>`).

We also define the following grammar for Coq import paths.

```
<import_path> ::= ident> {"." <ident>}*
```
They are currently only used in `rc::manual_proof` annotations.

Some of the constructs for type expressions require a notion of pattern. It is
defined as a tuple of variable name.
```
<pattern> ::=
  | "(" ")"
  | <ident (as variable name)>
  | "(" <ident (as variable name)> {"," <ident (as variable name)>}+ ")"
```

## Embedded Coq syntax

An important point about the syntax used in RefinedC annotations is that it is
eventually compiled down to Coq. A consequence of this is that pure Coq syntax
can (and sometimes must) be used among annotations. In particular, Coq is used
to express mathematical properties that are themselves part of function specs.
For example, you need to rely on Coq to express mathematical facts such as the
following: `n + m ≠ 42 × k`, `l1 ++ l2 ≠ []`, `P x ∧ Q y`. Inside annotations,
Coq syntax will be entered using different quotation mechanisms.
```
<pure_term> ::= "{" ... "}"    // (well-bracketed)
<iris_term> ::= "[" ... "]"    // (well-bracketed)
```
In particular, pure Coq terms will often be entered by simply surrounding them
with braces. No particular parsing is done for such terms, it is only enforced
that they are well-bracketed for braces. As a consequence `{n + m = n + m}` or
`{Α ∧ B}` are valid quoted Coq terms (if placed in a satisfactory scope). Note
that it is also possible to quote Coq terms using square brackets, but in that
case the wrapped Coq expression is expected to be an Iris proposition.

As it is very common to use Coq identifiers (e.g., variable or type names), it
is often not necessary to explicitly quote then using braces.
```
<coq_expr> ::=
  | <ident>
  | <pure_term>
```

## Type expressions

RefinedC type expressions are one of the main syntactic categories that we use
in annotations. They are defined as follows.
```
<type_expr> ::=
  | <ident (as type name)> {"<" ">"}?
  | <ty_name (as type name)> "<" <type_expr_arg> {"," <type_expr_arg>}* ">"
  | <coq_expr (as Coq value)> "@" <type_expr>
  | "∃" <ident (as variable name)> {":" <coq_expr (as Coq type)>}? "." <type_expr>
  | <type_expr> "&" <constr>
  | <pure_term (as type expression)>
  | "..."
  | "(" <tupe_expr> ")"
```

Note that type names include type constructors related to ownership. There are
three forms of pointer types:
 - owned pointers (of the form `&own<T>`),
 - shared pointers (of the form `&shr<T>`),
 - and fractional pointer (of the form `&frac<q, T>`).

### Type constuctor application

There are roughly eight different type expression constructors. The first one,
which encompasses the first two rules of `<type_expr>` is the application of a
defined type constructor to an arbitrary list of arguments (possibly zero, and
in that case the angle brackets surrounding the arguments may be left out).

Note that the arguments to defined type constructors are not type expressions,
but type expressions arguments (of class `<type_expr_arg>`).
```
<type_expr_arg> ::=
  | <type_expr>
  | "λ" <pattern> {":" <coq_expr (as Coq type)>}? "." <type_expr_arg>
```
They include type expressions themselves, but also allow for parametrized type
expressions, built using a λ-abstraction.

**Remark:** there is some special support for certain type constructors. There
is some discussion on that in a further section.

### Refinements

The fourth type expression constructor, of the form `v @ T`, is central to the
refinement type approach of RefinedC. It roughly denotes a singleton type. For
example, `{n} @ int<i32>` (or equivalently `n @ int<i32>`) denotes the type of
32-bits (signed) integers that are refined by mathematical integer `n`.

**Remark:** if type expression `T` is refined by a Coq value of (Coq) type `A`
then `T` is equivalent to `∃ v. v @ T` (using an existential type).

### Existential types

The fifth type expression constructor corresponds to existential types. In the
system, existential types can range over anything (including types). Note that
the type of the domain of existential quantifiers can be annotated using a Coq
type, but this is not mandatory (type inference often does a good job).

### Constrained types

The sixth type expression constructor corresponds to constrained types, having
the form `T & C`, where `C` is a constraint (see the next sub-section). Values
of type `T & C` are expected to both have type `T` and to satisfy `C`.

### Other constructors

The last three type expressions constructors respectively correspond to quoted
Coq code (interpreted as a type expression), type ellipses, and parentheses. A
type expression ellipsis is only meaningful in a `rc::typedef` annotation.

**Note on parsing priorities:** Binders always have the largest possible scope
and refinements (i.e., `@`) binds stronger than consrtains (i.e., `&`).

## Constraints

The syntax of constraints is defined below.
```
<constr> ::=
  | <iris_term (as Iris proposition)>
  | <pure_term (as Coq proposition)>
  | "∃" <ident (as variable name)> {":" <coq_expr (as Coq type)>}? "." <constr>
  | "own" <ident (as variable name)> ":" <type_expr>
  | "shr" <ident (as variable name)> ":" <type_expr>
  | "frac" <coq_expr (as ownstate)> <ident (as variable name)> ":" <type_expr>
  | <ident (as variable name)> ":" <type_expr>
  | "global" <ident (as C global variable name> ":" <type_expr>
```
A constraint can be formed using either:
 - a (quoted) Iris proposition,
 - a (quoted) Coq proposition,
 - an existential quantifier,
 - a pointer ownership statement (translated to a location type assignment),
 - a location type assignment for an owned location,
 - a location type assignment for a shared location,
 - a location type assignment for a frac location,
 - a value type assignment,
 - a typing constraint for a global variable.

**Remark:** a constraint of the form `{...}` is a short-hand for `[⌜...⌝]`, in
which `⌜...⌝` is the notation used to inject Coq proposition into `iProp` (the
type of Iris propositions).


# Special support

There is some special support for predefined type constructors:
 - `optional<ty>` is syntactic sugar for `optional<ty, {null}>`.
 - similarly, `optionalO<ty>` is syntactic sugar for  `optionalO<ty, {null}>`.
 - `struct<{layout}, ty1, ..., tyN>` builds a structure type, using the layout
   `layout` and the fields `ty1, ...,tyN`.

# Annotations using macros

The macro `rc_unfold_int(i)` can be used to extend the context with the
hypothesis that some integer parameter `i` is in the appropriate range.
Note that this is only useful if `i` has not yet been accessed, since the
hypothesis is added to the context on the first access.

# Annotations using comments

Special comments can be used to import external Coq dependencies as well as
for inlining Coq definitions in the generated code.

## Importing dependencies

To require a Coq module (`From <library> Require Import <modpath>`) in the
generated files, the following annotation can be used.
```c
//@rc::import <modpath> from <library>
```

By default the import is done in all the specification and proof files, but a
modifier can be used to only import the module in proof files, or only in the
code file.
```c
//@rc::import <modpath> from <library> (for proofs only)
//@rc::import <modpath> from <library> (for code only)
```

Note that it is not directly possible to import Coq modules from theories
defined in the same RefinedC project. To do so, one must first use a directive
like the following.
```c
//@rc::require <modpath>
```

## Context directive

The Coq context (in spec and proof sections) using the following annotation:
```c
//@rc::context <context_item> ... <context_item>
```

## Inlined Coq code

An arbitrary line of Coq code can be inlined in the generated specification
file using the following syntax (for single of multiple lines).
```c
//@rc::inlined <code line>

//@rc::inlined
//@<code line 1>
//@<code line 2>
//@<code line 3>
//@rc::end
```
With `rc::inlined`, the code is inserted at the beginning of the main section
of the specification file.

To inline Coq code at the beginning of the file (before the section) you can
use the tag `rc::inlined_prelude` instead. This is typically useful when you
want to define a notation (and want it to be available in proof files).

To inline Coq code at the end of the file (after the section) you can use the
tag `rc::inlined_final` instead.

## Type definition

A type definition without a struct can be made using the following syntax.
```c
//rc::typedef <ident> := <type_expr>
```

Refinements, parameters, and the `unfold_order` and `immovable` attributes
can be given as well as follows. Note that the types `R`, `S`, `X`, and `Y` are
parsed as `coq_expr`, so they might need to be wrapped in `{...}`.
```c
//rc::typedef (r:R, s:S) @ tree<x:X, y:Y> [unfold_order(90)] [immovable] := ...
```
