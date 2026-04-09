```vim
:lua vim.lsp.config('flap-ls', { cmd = {'/home/eoghan/.cargo/bin/flap-compiler', 'lsp'}, filetypes = {'flap'}, })

:lua vim.lsp.enable('flap-ls')

:set filetype=flap
```
