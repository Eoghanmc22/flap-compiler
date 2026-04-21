# Setting up the LSP

## Vim

```vim
:lua vim.lsp.config('flap-ls', { cmd = {'/home/eoghan/.cargo/bin/flap-compiler', 'lsp'}, filetypes = {'flap'}, })
:lua vim.lsp.enable('flap-ls')
:set filetype=flap
```

# Feature Ideas

- Compiler builtin for allocating data on heap
  - `char* my_string = box("This is a cool string")`
- Compiler builtin for printf and/or format strings
- Compiler builtin for preallocating c strings
  - maybe support `char* my_str = c"hello world"`
  - these would mostlikely include null termination
- Compiler builtin for dealing with NEXT_GLOBAL
- make `#include "std"` work regardless of pwd
- support code blocks/block expressions
- add `#[no_captures]`
- Allow having the highest bit set in a int literal
- Syntax for bitwise invert
