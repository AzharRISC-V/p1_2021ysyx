" http://www.ruanyifeng.com/blog/2018/09/vimrc.html

" 是否显示行号
set number
" 光标所在行显示绝对行号，其他行都为相对该行的行号
set relativenumber

" 光标所在行高亮
set cursorline

" 设置行宽，一行显示的字符数
set textwidth=80

" 自动折行
set wrap
" 关闭自动折行
" set nowrap

" 禁止在单词内部折行，只有空格、连词和其他标点符号才折行
set linebreak

" 指定折行处与编辑窗口的右边缘之间空出的字符数。
set wrapmargin=2

" 是否显示状态栏。0不显示，1只在多窗口显示，2显示。
set laststatus=2

" 是否显示光标的当前位置（行号、列号）
set ruler

set encoding=utf-8

" 是否自动缩进。按下回车，与上一行缩进保持一致。
set autoindent

" Tab键的空格数。
set tabstop=2

" 在文本上按下 >> 增加一级缩进，每一级的字符数
set shiftwidth=4

" 是否自动转换Tab为空格
set expandtab
" Tab转换为多少个空额
set softtabstop=2
