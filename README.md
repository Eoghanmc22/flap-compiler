# Flap Compiler

This is a simple compiler that targets the "clac" language

In CMU's 15-122 programming class, one of the assignments
is to implement an interperter for the "clac" language.
In short, it is a stack based language that uses reverse
polish notation syntax.

This compiles my "flap" language to "clac" instructions.
Flap is a very simple programming language. The only
control flow primitives flap has are if statements and
recursion. We dont even have early return, since that
can always we rewritten as an if expression. In flap,
blocks return the last expression they contain. If the
last expression ends with a semicolon, it returns void,
otherwise it returns what the expression evaluates to.
See the language grammar and sample code for more details.

## Installation

Make sure the rust programming language is installed

```sh
$ cargo +nightly install --git https://github.com/Eoghanmc22/flap-compiler.git --locked
```

## Usage

The compile subcommand takes a list of files to compile

```sh
$ flap-compiler compile [files to compile...]
```

## Architecture

We use the `pest` library to parse source code into tokens according to
our language grammer. We then traverse those tokens to generate an AST.
Next we have a type checking stage where we compute and validate all types
in the program. Then, if type checking passes, we traverse the AST again
and convert it to instructions in our intermediate repersentation. The IR
I made is a thin abstraction over the actual clac language. The main addition
is the ability to specify where the operands for an operation come from, since
in the clac language everything just operates with whatever is on the top of the
stack. The IR also includes many operands which are not implemented in clac,
but can be implemented interms of clac opcodes. The next stage in the compile
process is to convert the IR to actual clac tokens/opcodes, and do some postprocessing
steps. Clac does not support the nested function definitions my compiler generates,
while implementing if expressions for example. To get around this, we simply extract
such definitions to the start of the compiled clac file.
