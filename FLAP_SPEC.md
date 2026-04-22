This is an LLM generated document covering most of the features of flap.

# Flap Language Specification

> Reference for the bare-iron Minecraft port. Flap is a systems programming
> language that compiles to **clac** (a stack-based RPN language from CMU
> 15-122). Its surface syntax is close to C, but there are important semantic
> differences documented throughout this spec.

---

## Table of Contents

1. [Overview](#1-overview)
2. [Lexical Structure](#2-lexical-structure)
3. [Types](#3-types)
4. [Expressions](#4-expressions)
5. [Declarations and Statements](#5-declarations-and-statements)
6. [Control Flow](#6-control-flow)
7. [Functions](#7-functions)
8. [Memory Model](#8-memory-model)
9. [Defer](#9-defer)
10. [Attributes](#10-attributes)
11. [Preprocessor Directives](#11-preprocessor-directives)
12. [Standard Library](#12-standard-library)
13. [Differences from C](#13-differences-from-c)

---

## 1. Overview

Flap is a statically-typed, expression-oriented systems language. Programs are
compiled to clac, a stack-based RPN bytecode. The compiler is written in Rust
and lives in `flap-compiler/`.

A flap program is a sequence of top-level items: function definitions,
variable declarations, type definitions, and `#include` directives. Execution
starts at the first expression that is not a declaration — there is no implicit
`main` entry point unless one is explicitly called.

<!-- ```flap -->
<!-- // hello world -->
<!-- #include "std/io.flap" -->
<!-- write(STDOUT, "Hello, world!\n\0", 15); -->
<!-- ``` -->

---

## 2. Lexical Structure

### Comments

```flap
// single-line comment
/* multi-line
   comment */
```

### Literals

| Form | Examples |
|------|---------|
| Decimal integer | `42`, `1_000_000` |
| Hex integer | `0xFF`, `0xDEAD_BEEF` |
| Binary integer | `0b1010`, `0b1111_0000` |
| Octal integer | `0o755` |
| Boolean | `true`, `false` |
| Character | `'a'`, `'\n'` |
| String | `"hello\n\0"` (null-terminator must be explicit) |

Underscores are allowed anywhere in a numeric literal and are ignored.

### Identifiers

Identifiers start with a letter or `_`, followed by any number of letters,
digits, or `_`.

### Keywords

```
struct  if      else    while   for     loop    defer
const   auto    typedef include sizeof  sizeof_packed  __LINE__
true    false   void    int     char    bool    NULL
box     global
```

---

## 3. Types

### Primitive types

| Type | Description |
|------|-------------|
| `int` | Machine-word integer (64-bits) |
| `char` | Single byte |
| `bool` | Boolean (`true` / `false`) |
| `void` | No value; only valid as a function return type |

There is a single integer size (one machine word). There are no `short`,
`long`, `unsigned`, `float`, or `double` types. Floating-point arithmetic is
not supported at all.

### Pointer types

```flap
int *p        // pointer to int
char *s       // pointer to char (conventional string type)
void *ptr     // generic pointer — implicitly coerces to/from any pointer type
int **pp      // pointer to pointer to int
```

Pointer arithmetic is supported: `p + n`, `p - n`.

### Array types

```flap
int[5] arr    // fixed-size array of 5 ints (stack-allocated)
```

Arrays have a compile-time fixed size. There are no variable-length arrays.
Array size is part of the type; `int[5]` and `int[3]` are distinct types.

Array elements are accessed with `arr[i]`. Arrays are value types — assigning
one array to another copies all elements.

### Struct types

```flap
typedef struct {
    int age;
    char *name;
    struct {
        int x;
        int y;
    } pos;
} Player;
```

Structs are value types. Nested anonymous structs are allowed as field types.
Fields are accessed with `.` or `->` (through a pointer).

<!-- ### Tuple types -->
<!---->
<!-- Unnamed struct-like types used primarily as function return values: -->
<!---->
<!-- ```flap -->
<!-- typedef (int, char *) pair; -->
<!-- ``` -->
<!---->
<!-- *(Tuple syntax is in the grammar; usage mirrors anonymous structs.)* -->

### `void *` and `NULL`

`NULL` is an alias for `(void *)0`. Any pointer type can be compared against
`NULL`. `void *` implicitly coerces to and from all other pointer types — no
cast is required at assignment. An explicit cast is still needed to dereference
a `void *` (since the type to dereference as must be stated).

### `typedef`

```flap
typedef <type> <name>;
typedef struct { ... } <name>;
```

Typedefs create an alias. They cannot be used before they are declared within the
same file.

### `auto`

```flap
auto header = "HTTP/1.1 200 OK\r\n";
```

`auto` infers the type from the initializer expression. It is always required
to have an initializer.

### `sizeof` and `sizeof_packed`

```flap
sizeof(expr)        // size of expr's type, in machine words
sizeof<Type>        // size of named type, in machine words
sizeof_packed(expr) // size in bytes, ignoring padding
```

`sizeof_packed` is the primary way to get a byte count for string/buffer
lengths.

### `box` builtin

```flap
box(expr)           // Allocates expr on the heap and return a pointer to it
```

### `global` builtin

```flap
global(width_bytes)           // Returns a pointer to a place of size width_bytes, 
global<Type>                  // Returns a pointer to a place large enough for Type in repr flap (ie the on stack repr)
```

Every call site gets a unique pointer, but unlike malloc a given call site will always return the same value.
The global builtin is const compatible. It is useful for allocinting places to store shared global mutable state.
Since the pointer returned by `global` is comptime known, it avoids the capturing overhead incured when
emulating this behaivor by capturing a variable defined at top level.

```flap
void example() {
    // Will print the same number each time this function is called
    print((int) global(0)); 
}

// Will print a unique pointer
print((int) global(0)); 

// Will print a unique pointer
print((int) global(0)); 

// Will print same pointer twice
example();
example();
```

---

## 4. Expressions

**Everything in flap that produces a value is an expression.** This includes
`if`, blocks `{ ... }`, and function bodies.

<!-- ### Block expressions -->
<!---->
<!-- A block `{ e1; e2; e3 }` evaluates each item in order and returns the last -->
<!-- one. A trailing semicolon discards the value and makes the block return `void`. -->
<!---->
<!-- ```flap -->
<!-- int x = { int tmp = 5; tmp * 2 };   // x == 10 -->
<!-- { print(x); };                       // void block (trailing ;) -->
<!-- ``` -->

### Operator precedence (high to low)

| Level | Operators |
|-------|-----------|
| Postfix | `expr.field`, `expr->field`, `expr[i]`, `f(args)` |
| Prefix | `~expr`, `-expr`, `!expr`, `*expr`, `&expr`, `(Type)expr` |
| Multiplicative | `*`, `/`, `%` |
| Additive | `+`, `-` |
| Shift | `<<`, `>>` |
| Bitwise AND | `&` |
| Comparison | `<`, `<=`, `>`, `>=` |
| Equality | `==`, `!=` |
| Logical AND | `&&` |
| Logical OR | `\|\|` |
| Assignment | `=` |

**Missing operators (not in flap):** `|` (bitwise OR), `^` (bitwise XOR),
`~` (bitwise NOT), `?:` (ternary). There is also no `float`/`double`.

**`&` restriction:** The right-hand operand of `&` must be a compile-time
constant — either a literal (`0xFF`, `-4`) or a `const int` that the compiler
can inline. `a & b` where `b` is a runtime variable is **not supported**.

**Integer literal range:** Literals are parsed as signed 64-bit. Values
≥ 2^63 (e.g. `0x9e3779b97f4a7c15`) overflow and are rejected. Represent
them as their signed equivalent (subtract 2^64): the negative hex of a
large unsigned constant is `-(2^64 - value)`.

**`&` on local variables:** `&local_var` is not supported (only
`&(*ptr)` which simplifies back to the pointer). Use malloc to get a pointer
to heap-allocated storage when you need to pass a pointer to a local value.

All binary operators are left-associative.

### Assignment

Assignment is an expression that returns `void`:

```flap
x = 5;
*ptr = value;
arr[i] = arr[i] + 1;
s->field = 42;
```

There are no compound assignment operators (`+=`, `++`, etc.). Write `x = x + 1`.

### Cast

```flap
(int)char_val
(char *)malloc(n)
(void *)ptr
```

Casts are explicit. There are no implicit numeric promotions or pointer
conversions (except `void *` coercing to/from any pointer).

### Address-of and dereference

```flap
int *p = &x->y;    // take address of variable
int v = *p;        // dereference
*p = 10;           // write through pointer
```

### Struct literals

```flap
Person p = struct {
    age = 30;
    name = NULL;
};
```

All fields must be named. Fields may be listed in any order unless the struct is defined using the `inorder` keyword.
For structs that are not `inorder`, their fields are represented in alphabetical order

### Array literals

```flap
int[5] arr = [1, 5, 2, 1, 3];
```

Array literals require all elements to be provided.

### String literals

Strings are `char[len]` arrays. A null terminator is **not** appended automatically — include `\0` explicitly.
To get a pointer to a string, it currently must be manually assigned to a pointer on the stack.

```flap
auto greeting = "Hello!\n\0";

char *page = malloc(sizeof_packed(greeting));
// This will memcopy the stack allocated string onto the heap
*page = greeting;
```

---

## 5. Declarations and Statements

### Variable declaration

```flap
int x = 5;
auto s = "hello\0";
auto pair = compute();
```

Variables must be initialised at declaration. There is no uninitialized state.

A variable name can be re-declared in the same scope; the new declaration
shadows the previous binding. Type checking uses SSA-style versioning
internally:

```flap
int x = 5;
int x = x + 1;   // legal — re-declares x with new value
```

### `const` declaration

```flap
const int MAX_PLAYERS = 16;
const char *TAG = "server\0";
```

`const` variables are immutable. They can appear at any scope.

---

## 6. Control Flow

### `if` expression

`if` is an expression returning the value of the taken branch. All branches
must have compatible types (or the expression must be used in a void context).

```flap
int abs_val = if (x < 0) { -x } else { x };

// void if (no else required):
if (condition) {
    do_something();
}
```

`else if` chains are supported:

```flap
if (a) {
    ...
} else if (b) {
    ...
} else {
    ...
}
```

### `while` loop

```flap
while (condition) {
    body;
}
```

`while` always returns `void`.

### `for` loop

C-style for loop. The init clause is a single declaration or expression; the
update clause is an expression:

```flap
for (int i = 0; i < n; i = i + 1) {
    process(arr[i]);
}
```

`for` always returns `void`.

### `loop` (infinite loop)

```flap
loop {
    int client = accept(server_fd, (sockaddr *)NULL, (int *)NULL);
    handle(client);
}
```

Exits only via a function that does not return (e.g., `exit`).

There are no `break` or `continue` keywords. Restructure using functions or
conditional guards instead.

---

## 7. Functions

### Definition syntax

```flap
ReturnType name(Type param1, Type param2) {
    body
}
```

The return value is the last expression in the body. A tail expressiong with a trailing `;` makes the
function return `void`. There is no `return` keyword, If expression must be used to emulate early returns if necessary.

```flap
int add(int a, int b) { a + b }         // returns a + b
void log(char *msg) { write(STDOUT, msg, strlen(msg)); }  // void (trailing ;)
```

### Nested functions

Functions may be defined inside other functions. The inner function is in scope
for the remainder of the enclosing block:

```flap
int fact(int n) {
    int go(int acc, int i) {
        if (i <= 1) { acc } else { go(acc * i, i - 1) }
    }
    go(1, n)
}
```

### Variable capture (closures)

A nested function can reference variables from enclosing scopes. Captures are
read-only by default. If the inner function mutates a captured variable the
compiler tracks this as `ReadWrite`:

```flap
int counter = 0;

void increment() {
    counter = counter + 1;   // ReadWrite capture of counter
}

increment();
increment();
print(counter);   // 2
```

Captures from the enclosing scope are implicitly available — no explicit
capture list is needed.

### Recursion

Recursive calls are fully supported, including mutual recursion between
nested functions.

### Top-level code

Code at top-level that is not a declaration is executed as program startup
logic in source order:

```flap
int server_fd = socket(AF_INET, SOCK_STREAM, 0);
bind(server_fd, ...);
listen(server_fd, 3);
accept_loop(server_fd);
```

---

## 8. Memory Model

### Stack allocation

All locals are stack-allocated. Composite types (structs, arrays) are stored as
multiple consecutive words on the stack. Assignment copies the entire value.

### Heap allocation

```flap
char *buf = malloc(n);    // allocate n bytes, returns char *
buf = realloc(buf, n2);   // resize
free(buf);                // release
```

`malloc` is implemented via `mmap`; `free` via `munmap`; `realloc` via
`mremap`. There is no garbage collector.

### Pointer operations

```flap
char *p = malloc(64);
*p = "prefix\0";                // write string at p[0]
*(p + 7) = "suffix\0";          // write at byte offset 7
char c = p[3];                  // index dereference (sugar for *(p+3))
int n = (int)p;                 // pointer-to-integer cast
```

Pointer arithmetic is in units of the width of the inner type, consistent with C.

### Struct on the heap

```flap
Player *pl = malloc(sizeof<Player>);
*pl = struct { age = 20; name = (char *)NULL; };
pl->age = 21;
```

`sizeof(expr)` or `sizeof<type>` gives the width when on the stack. For packed sizes (ie for size after copying to the heap) use `sizeof_packed`.

This is because, for example, `char` is repersented as a 64-bit `int` on the stack, but then a 8-bit word when written to a pointer.

### `void *` coerces implicitly

`void *` implicitly coerces to and from any other pointer type. No cast is
needed at assignment:

```flap
Player *p = malloc(sizeof<Player>);   // void * → Player * implicitly
void *v = p;                          // Player * → void * implicitly
```

A cast is still required to *dereference* a `void *` (the pointee type must
be stated explicitly).

### Captures and Mutation

Any variables that are captures by a block in flap are passed as an arguement to that block, and all of its parent blocks.
This is because flap is internally implemented in a rather functional manner.
More over, mutation is implemented by including the new values of captured mutated variables in the return type of that block.
This means that capturing variables that are not comptime known and especially mutation have non-trivial overhead.
Putting the `#[no_captures]` attribute on a function makes it a compile error for it to capture a variable.

---

## 9. Defer

`defer` registers a block to execute when the enclosing scope exits. Multiple
defers execute in LIFO order (last-registered runs first):

```flap
int fd = open(path, O_RDONLY, 0);
defer { close(fd); }

char *buf = malloc(4096);
defer { free(buf); }

// ... use fd and buf ...
// on scope exit: free(buf) runs, then close(fd)
```

Deferred blocks capture variables by reference — they see the variable's value
at the time the defer fires, not when it was registered:

```flap
int x = 5;
defer { print(x); }   // prints whatever x is when scope exits
x = 6;
int x = 10;           // re-declare x (new version)
// defer prints 6 (last modification to the version captured at defer time)
```

---

## 10. Attributes

Function attributes appear on the line before the definition:

```flap
#[no_mangle]
int entry_point(int argc, char **argv) { ... }
```

| Attribute | Meaning |
|-----------|---------|
| `#[no_mangle]` | Export to clac output with the exact function name (required for the entry point and FFI) |
| `#[allow_underflow]` | Suppress stack-underflow safety checks for this function (COMPILER INTERNAL) |
| `#[naked]` | Emit function body directly with no prologue/epilogue (COMPILER INTERNAL) |

---

## 11. Preprocessor Directives

```flap
#include "path/to/file.flap"
#include "../std"              // includes std/mod.flap (directory shorthand)
```

`#include` performs textual inclusion. There is no `#define`, `#ifdef`, or
macro system. Use `const` for named constants and `typedef` for type aliases.

`__LINE__` expands to the current line number as an integer literal.

---

## 12. Standard Library

The standard library lives in `flap-compiler/std/`. Include it with:

```flap
#include "../std"
```

Or include individual modules:

```flap
#include "../std/io.flap"
#include "../std/malloc.flap"
```

### Key modules

| Module | Contents |
|--------|----------|
| `syscall.flap` | Wrappers around raw linux interface |
| `malloc.flap` | `malloc`, `free`, `realloc` |
| `memory.flap` | `memcpy_char`, `memset`, page utilities |
| `io.flap` | `read_all`, `read_all2`, `write_all`, `copy_all`; constants `STDIN`, `STDOUT`, `STDERR` |
| `strings.flap` | `strlen`, `strcmp`, `strcpy`, `convert_int_to_string` |
| `socket.flap` | `socket`, `bind`, `listen`, `accept`, `connect`, `setsockopt`; constants `AF_INET`, `SOCK_STREAM`, etc. |
| `process.flap` | `fork`, `exit`, `getpid` |
| `math.flap` | Integer arithmetic utilities |
| `integer.flap` | `int_width` (machine word size in bytes) |
| `list_int.flap` | Dynamic array of `int` (`list_int`) |
| `list_string.flap` | Dynamic array of `char *` (`list_string`) |
| `map_int.flap` | Hash map `int → int` |
| `map_string.flap` | Hash map `char * → char *` |
| `hash.flap` | Hash functions |
| `rand.flap` | PRNG |
| `assert.flap` | `assert(cond)` |
| `buf.flap` | Byte buffer for wayland |
| `env.flap` | `parse_args` |
| `constants.flap` | System constants (`O_RDONLY`, `PROT_READ`, …) |
| `bitwise.flap` | `bwand`, `bwxor`, `bwor` |

---

## 13. Differences from C

This section is the primary reference for porting C code to Flap.

### 13.1 Expression-oriented blocks

In C, `{}` braces form a *statement* block with no value. In Flap, a block is
an *expression* whose value is its last sub-expression. A trailing semicolon
makes the value `void`.

```c
// C
int x;
if (cond) { x = 1; } else { x = 2; }
```

```flap
// Flap
int x = if (cond) { 1 } else { 2 };
```

### 13.2 No `return` keyword

The return value of a function is the last expression in its body. There is no
`return` statement. To return early, restructure using nested functions or
refactor the control flow.

```c
// C
int clamp(int v, int lo, int hi) {
    if (v < lo) return lo;
    if (v > hi) return hi;
    return v;
}
```

```flap
// Flap
int clamp(int v, int lo, int hi) {
    if (v < lo) { lo } else if (v > hi) { hi } else { v }
}
```

### 13.3 No `break` or `continue`

There are no loop-control keywords. Factor the early-exit condition into the
loop guard or use a helper function that returns from the inner loop body.

```c
// C — find first match
for (int i = 0; i < n; i++) {
    if (arr[i] == target) { found = i; break; }
}
```

```flap
// Flap — use a recursive helper
int find(int *arr, int n, int target, int i) {
    if (i >= n)          { -1 }
    else if (arr[i] == target) { i }
    else { find(arr, n, target, i + 1) }
}
int found = find(arr, n, target, 0);
```

### 13.4 No compound assignment or increment operators

Replace `x++`, `x += n`, `x -= n`, etc. with explicit `x = x + 1`, `x = x + n`.

```c
i++;          // C
i = i + 1;   // Flap
```

### 13.5 Nested functions and closures

Flap supports function definitions inside functions, with implicit capture of
enclosing variables. C does not (without GCC extensions).

```flap
void process(int *data, int n) {
    int sum = 0;
    void add(int v) { sum = sum + v; }   // captures sum
    for (int i = 0; i < n; i = i + 1) { add(data[i]); }
    print(sum);
}
```

### 13.6 Defer (no `goto cleanup`)

The C pattern of `goto cleanup` / manual cleanup labels is replaced by `defer`:

```c
// C
int result = -1;
FILE *f = fopen(path, "r");
if (!f) goto done;
char *buf = malloc(1024);
if (!buf) goto close_f;
// ... use f and buf ...
result = 0;
free(buf);
close_f: fclose(f);
done: return result;
```

```flap
// Flap
int fd = open(path, O_RDONLY, 0);
defer { close(fd); }
char *buf = malloc(1024);
defer { free(buf); }
// ... use fd and buf ...
// cleanup runs automatically
```

### 13.7 No implicit type conversions (except `void *`)

C silently converts between integer types and promotes `char` to `int`. Flap
requires explicit casts for numeric type changes, but `void *` implicitly
coerces to and from all other pointer types (unlike C, where this is also
implicit, but unlike Flap's treatment of other pointer pairs).

```c
char c = 65;          // C: implicit int→char
int n = c;            // C: implicit char→int
```

```flap
char c = (char)65;
int n = (int)c;
// void * coerces freely — no cast needed at pointer assignment:
int *p = malloc(n);   // fine; malloc returns void * which coerces to int *
```

### 13.8 Struct initialization uses named fields, not positional

C designated initializers (`.field = val`) are optional. Flap requires the
`struct { field = val; }` literal form — positional initialization is not
supported.

```c
// C
Player p = { .age = 20, .name = NULL };
```

```flap
// Flap
Player p = struct { age = 20; name = (char *)NULL; };
```

### 13.9 No `enum`

There is no `enum` keyword. Use `const int` declarations instead:

```c
// C
typedef enum { STATE_LOGIN, STATE_PLAY } State;
```

```flap
// Flap
const int STATE_LOGIN = 0;
const int STATE_PLAY  = 1;
typedef int State;
```

### 13.10 No `switch` statement

Use `if`/`else if` chains instead.

### 13.11 No `#define` macros

There is no preprocessor macro system. Use:
- `const` for named constants
- `typedef` for type aliases
- Inline functions for function-like macros

### 13.12 No variadic functions

There is no `...` / `va_list` mechanism. Functions have fixed arity.

### 13.13 Array semantics

In C, arrays decay to pointers when passed to functions. In Flap, arrays are
true value types — passing an array copies all elements. To pass a large array
efficiently use pointer to a heap allocated array instead.

### 13.14 Single integer type and no floating-point

There is only `int` (64-bit machine word) and `char` (byte). There are no unsigned
types, no 16-bit types, and no floating-point types (`float`, `double`).
Use bitwise masking where unsigned behaviour is needed: `val & 0xFF`,
`val & 0xFFFF`.

### 13.14a Missing bitwise operators

Flap has `&` (bitwise AND, rhs must be comptime known), `~` (bitwise NOT), and `<<`/`>>` (shifts) but **not**:
- `|` — bitwise OR
- `^` — bitwise XOR

General bitwise AND, as well as bitwise OR and bitwise XOR are implemented in software in `std/bitwise.flap`.

**XOR of runtime values** is entirely impossible in flap — neither `^` nor
any workaround using `&` works when both operands are non-const. Replace
xorshift-based PRNGs with LCG. For bit-manipulation that requires XOR,
restructure logic to avoid it.

<!-- ### 13.15 No `NULL` macro — use cast or constant -->
<!---->
<!-- `NULL` is defined in the standard library as `(void *)0`. Without including -->
<!-- the standard library, write `(char *)0`, `(int *)0`, etc. -->

### 13.16 String literals require explicit null terminator

C appends `\0` automatically. Flap does not:

```c
char *s = "hello";          // C: "hello\0" (6 bytes)
```

```flap
auto s = "hello\0";        // Flap: must be explicit
```

### 13.17 `sizeof` returns byte width of on stack representation

Use `sizeof_packed` for size after copying to the heap:

<!-- ```flap -->
<!-- write(fd, msg, sizeof_packed(msg));   // byte count -->
<!-- int stack_repr_width = sizeof(msg);   //  -->
<!-- ``` -->

### 13.18 No `static` or `extern`

There is no `static` storage class. All globals are implicitly top-level.
There is no linkage mechanism beyond `#include` (textual inclusion).

---

## Appendix: Quick translation table

| C construct | Flap equivalent |
|------------|-----------------|
| `return x;` | Last expression in function body |
| `break;` | Refactor loop; use recursive helper |
| `continue;` | Refactor loop |
| `x++` / `x--` | `x = x + 1` / `x = x - 1` |
| `x += n` | `x = x + n` |
| `switch (x) { case A: ... }` | `if (x == A) { ... } else if ...` |
| `#define NAME val` | `const int NAME = val;` |
| `#define MACRO(x) (x*2)` | `int MACRO(int x) { x * 2 }` |
| `enum { A, B, C }` | `const int A = 0; const int B = 1; ...` |
| `goto cleanup;` | `defer { ... }` |
| `(void *)malloc(n)` | `malloc(n)` (`void *` coerces implicitly; no cast needed) |
| `sizeof(T)` (bytes) | `sizeof<T>` or `sizeof_packed<T>` |
| `static int x = 0;` | Top-level `int x = 0;` |
| Designated init `.f = v` | `struct { f = v; }` literal |
| `char s[] = "hi";` | `char *s = "hi\0";` |
| Implicit `int`↔`char` | Explicit `(int)c` / `(char)n` |
