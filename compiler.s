%define T_UNDEFINED 0
%define T_VOID 1
%define T_NIL 2
%define T_RATIONAL 3
%define T_FLOAT 4
%define T_BOOL 5
%define T_CHAR 6
%define T_STRING 7
%define T_SYMBOL 8
%define T_CLOSURE 9
%define T_PAIR 10
%define T_VECTOR 11
%define T_MAGIC qword SOB_NIL_ADDRESS

%define TYPE_SIZE 1
%define WORD_SIZE 8
	
%define KB(n) n*1024
%define MB(n) 1024*KB(n)
%define GB(n) 1024*MB(n)


%macro SKIP_TYPE_TAG 2
	mov %1, qword [%2+TYPE_SIZE]	
%endmacro	

%define NUMERATOR SKIP_TYPE_TAG

%macro DENOMINATOR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%macro CHAR_VAL 2
	movzx %1, byte [%2+TYPE_SIZE]
%endmacro

%define FLOAT_VAL SKIP_TYPE_TAG

%define STRING_LENGTH SKIP_TYPE_TAG
%define VECTOR_LENGTH SKIP_TYPE_TAG

%define SYMBOL_VAL SKIP_TYPE_TAG

%macro STRING_ELEMENTS 2
	lea %1, [%2+TYPE_SIZE+WORD_SIZE]
%endmacro
%define VECTOR_ELEMENTS STRING_ELEMENTS

%define CAR SKIP_TYPE_TAG

%macro CDR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define CLOSURE_ENV CAR

%define CLOSURE_CODE CDR

;return address of first optional variable on the stack
%define OPT_VAR(n) rbp + (3 + n) * WORD_SIZE
%define PVAR(minor) qword [rbp + (4+minor) * WORD_SIZE]
%define PARAMS_COUNT qword [rbp + 3 * WORD_SIZE]
%define RET_ADDR qword [rbp + 1 * WORD_SIZE]
%define PARAMS_ARRAY rbp + 4 * WORD_SIZE
%define CONST(n) qword const_tbl + n
%define FVAR(n) qword [fvar_tbl + n * WORD_SIZE]
;return address of bound variable in register %1 .
;%2 = major, %3 = minor
%macro BVAR 3
	mov %1, LEXICAL_ENVIRONMENT ; %1 contains address of vector<vector<pointers> represents the enclosing environment
	mov %1, VECTOR_REF(%1, %2) ; %1 contains address of vector in which var was defined
	mov %1, VECTOR_REF(%1, %3) ; %1 contains address of bound variable
%endmacro

%define VECTOR_REF(r, i) qword [r + TYPE_SIZE + WORD_SIZE + i * WORD_SIZE]
%define VECTOR_SIZE(r) qword [r + TYPE_SIZE]
%define LEXICAL_ENVIRONMENT qword [rbp + 2 * WORD_SIZE]
; %1 = offset of the parameter
%macro PSET 1
	mov PVAR(%1), rax
	mov rax, SOB_VOID_ADDRESS
%endmacro

; set address of bound variable in register %1.
; %2 = major, %3 = minor, 
; %4 = src (address of evaluated expression)
%macro BSET 4
	mov %1, LEXICAL_ENVIRONMENT
	mov %1, VECTOR_REF(%1, %2) 
	lea %1, [%1 + + TYPE_SIZE + WORD_SIZE + %3 * WORD_SIZE] ; %1 contains address of bound variable IN THE VECTOR
	mov [%1], %4
	mov rax, SOB_VOID_ADDRESS
%endmacro

; %1 = offset of free var
%macro FSET 1
	mov FVAR(%1), rax 
	mov rax, SOB_VOID_ADDRESS
%endmacro

; returns %2 allocated bytes in register %1
; Supports using with %1 = %2
%macro MALLOC 2
	add qword [malloc_pointer], %2
	push %2
	mov %1, qword [malloc_pointer]
	sub %1, [rsp]
	add rsp, 8
%endmacro
	
; Creates a short SOB with the
; value %2
; Returns the result in register %1
%macro MAKE_CHAR_VALUE 2
	MALLOC %1, 1+TYPE_SIZE
	mov byte [%1], T_CHAR
	mov byte [%1+TYPE_SIZE], %2
%endmacro

; Creates a long SOB with the
; value %2 and type %3.
; Returns the result in register %1
%macro MAKE_LONG_VALUE 3
	MALLOC %1, TYPE_SIZE+WORD_SIZE
	mov byte [%1], %3
	mov qword [%1+TYPE_SIZE], %2
%endmacro

%define MAKE_FLOAT(r,val) MAKE_LONG_VALUE r, val, T_FLOAT
%define MAKE_CHAR(r,val) MAKE_CHAR_VALUE r, val

; Create a string of length %2
; from char %3.
; Stores result in register %1
%macro MAKE_STRING 3
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_STRING
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1,WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%str_loop:
	jz %%str_loop_end
	dec rcx
	mov byte [%1+rcx], %3
	jmp %%str_loop
%%str_loop_end:
	pop rcx
	sub %1, WORD_SIZE+TYPE_SIZE
%endmacro

; Create a vector of length %2 - register!
; from array of elements in register %3 of length %4
; Store result in register %1
; %5 offset to start writing
%macro MAKE_VECTOR 5
	push %2
	shl %2, 3; each element is of size 8 bytes
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_VECTOR
	pop %2 ; restore register %2 state
	mov qword [%1+TYPE_SIZE], %2

    push rbx
    push %1
    add %1, WORD_SIZE+TYPE_SIZE
%%vector_loop:
    cmp %4, 0
    jz %%vector_loop_end
    mov rbx, qword [%3]
    mov qword [%1 + %5 * WORD_SIZE], rbx
    add %1, WORD_SIZE
    add %3, WORD_SIZE
    dec %4
    jmp %%vector_loop
%%vector_loop_end:
    pop %1
    pop rbx
%endmacro

; return in register %1 address of empty env: vector contains only SOB_NIL_ADDRESS
%macro MAKE_EMPTY_ENV 1
lea %1, [2 * WORD_SIZE + TYPE_SIZE]
MALLOC %1, %1
mov byte [%1], T_VECTOR
mov qword [%1+TYPE_SIZE], 1
mov qword [%1 + TYPE_SIZE + WORD_SIZE], SOB_NIL_ADDRESS
%endmacro

; Create a list of length %2 - register!
; from array of elements in register %3
; Store result in register %1
%macro MAKE_SCM_LIST 3
	push %2
	push %3
	push r11 ; car
	push r12
	mov r12, T_MAGIC ;cdr
	%%scm_list_loop:
		cmp %2, 0
		jz %%scm_list_loop_end
		mov r11, [%3]
		MAKE_PAIR(%1, r11, r12)
		mov r12, %1
		dec %2
		sub %3, WORD_SIZE
		jmp %%scm_list_loop
	%%scm_list_loop_end:
		pop r12
		pop r11
		pop %3
		pop %2
%endmacro

; %1 = size of frame (constant)
%macro SHIFT_FRAME 1
	push rax
	push r9
	push r10
	push rbx
	mov rdx, [rbp]
	mov rcx, PARAMS_COUNT
	add rcx, 5
	mov r9, %1
	mov r10, WORD_SIZE
	%%shift_frame_loop:
		cmp r9, 0
		jz %%shift_frame_loop_end
		dec rcx
		mov rbx, rbp
		sub rbx, r10
		mov rbx, qword [rbx]
		mov [rbp + rcx * WORD_SIZE], rbx
		dec r9
		add r10, WORD_SIZE
		jmp %%shift_frame_loop
	%%shift_frame_loop_end:
		pop rbx
		pop r10
		pop r9
		pop rax
		lea rsp, [rbp + rcx * WORD_SIZE]
		mov rbp, rdx
%endmacro


;%1 = register contains number of parameters of the variadic lambda
;%2 = register contains number of pushed parameters (ON THE STACK)
%macro ADJUST_STACK_FRAME 2
	; save current registers state
	push %1
	push %2
	push rsi
	push rdi
	push rdx
	push rcx
	; if %1 > %2, there is nothing to adjust.
	cmp %1, %2
	jg %%run_end
	%%run:
		lea rsi, [rbp + (3 + %2) * WORD_SIZE]; address of parameter before magic
		mov rcx, %2 ; set rcx to the number of optional argument
		sub rcx, %1
		inc rcx 
		MAKE_SCM_LIST rdi, rcx, rsi
		mov qword [rsi], rdi ; replace magic with list contains all optional argument
		mov qword [rbp + 3 * WORD_SIZE], %1 ; set param count (on the stack) to %1
		sub rsi, WORD_SIZE ; next location
		lea rdi, [rbp + (2 + %1) * WORD_SIZE] ; next data
		lea rcx, [%1 + 3] ; number of elements to copy from the stack
		%%run_loop:
				cmp rcx, 0
				jle %%run_loop_end
				mov rdx, [rdi]
				mov [rsi], rdx
				sub rsi, WORD_SIZE
				sub rdi, WORD_SIZE
				dec rcx
				jmp %%run_loop
		%%run_loop_end:
				; set rbp to point to the new frame.
				; restore registers state
				add rsi, WORD_SIZE
				mov rbp, rsi
	%%run_end:
		pop rcx
		pop rdx
		pop rdi
		pop rsi
		pop %2
		pop %1
		; set rsp to point to the new frame.
		mov rsp, rbp
	; rest of body execution
%endmacro

; %1 is a register contains address of scheme list (nested pairs)
; %2 register used to dereference car values
; %3 regiser used as accumulator of list length
%macro PUSH_APPLY_LIST_ELEMENTS 3
	xor %3, %3
	mov r13, SOB_NIL_ADDRESS
	%%reverse_list_elements_loop:
		cmp %1, SOB_NIL_ADDRESS
		je %%push_reversed_list_elements_loop
		CAR %2, %1
		MAKE_PAIR(r14, %2, r13)
		mov r13, r14
		CDR %1, %1
		inc %3
		jmp %%reverse_list_elements_loop
	%%push_reversed_list_elements_loop:
		cmp r13, SOB_NIL_ADDRESS
		je %%push_reversed_list_elements_loop_end
		CAR %2, r13
		push %2
		CDR r13, r13
		jmp %%push_reversed_list_elements_loop
	%%push_reversed_list_elements_loop_end:
%endmacro

; push arguments besides proc and lst
%macro PUSH_APPLY_ELEMENTS 1
	mov r14, %1
	%%push_apply_elements_loop:
		cmp r14, 0
		jz %%push_apply_elements_loop_end
		push PVAR(r14)
		dec r14
		jmp %%push_apply_elements_loop 
	%%push_apply_elements_loop_end:
%endmacro

%macro MAKE_LITERAL_VECTOR 0-*
	db T_VECTOR
	dq %0
%rep %0
	dq %1
%rotate 1
%endrep
%endmacro

;;; Creates a SOB with tag %2 
;;; from two pointers %3 and %4
;;; Stores result in register %1
%macro MAKE_TWO_WORDS 4 
        MALLOC %1, TYPE_SIZE+WORD_SIZE*2
        mov byte [%1], %2
        mov qword [%1+TYPE_SIZE], %3
        mov qword [%1+TYPE_SIZE+WORD_SIZE], %4
%endmacro

%macro MAKE_WORDS_LIT 3
	db %1
	dq %2
	dq %3
%endmacro

%macro MAKE_LITERAL 2
	db %1
	%2
%endmacro

%define MAKE_RATIONAL(r, num, den) \
	MAKE_TWO_WORDS r, T_RATIONAL, num, den

%define MAKE_LITERAL_RATIONAL(num, den) \
	MAKE_WORDS_LIT T_RATIONAL, num, den

%define MAKE_LITERAL_FLOAT(val) \
		MAKE_LITERAL T_FLOAT, dq val

%define MAKE_PAIR(r, car, cdr) \
        MAKE_TWO_WORDS r, T_PAIR, car, cdr

%define MAKE_LITERAL_PAIR(car, cdr) \
        MAKE_WORDS_LIT T_PAIR, car, cdr

%define MAKE_CLOSURE(r, env, body) \
        MAKE_TWO_WORDS r, T_CLOSURE, env, body

%define MAKE_LITERAL_SYMBOL(val) \
	MAKE_LITERAL T_SYMBOL, dq val

%define MAKE_LITERAL_CHAR(val) \
	MAKE_LITERAL T_CHAR, db val

%macro MAKE_LITERAL_STRING 1+
	db T_STRING
	dq (%%end_str - %%str)
	%%str:
		db %1
	%%end_str:
%endmacro

;;; Macros and routines for printing Scheme OBjects to STDOUT
%define CHAR_NUL 0
%define CHAR_TAB 9
%define CHAR_NEWLINE 10
%define CHAR_PAGE 12
%define CHAR_RETURN 13
%define CHAR_SPACE 32
%define CHAR_DOUBLEQUOTE 34
%define CHAR_BACKSLASH 92
	
extern printf, malloc
global write_sob, write_sob_if_not_void

write_sob_undefined:
	push rbp
	mov rbp, rsp

	mov rax, qword 0
	mov rdi, .undefined
	call printf

	pop rbp
	ret

section .data
.undefined:
	db "#<undefined>", 0

section .text
write_sob_rational:
	push rbp
	mov rbp, rsp

	mov rdx, rsi
	NUMERATOR rsi, rdx
	DENOMINATOR rdx, rdx
	
	cmp rdx, 1
	jne .print_fraction

	mov rdi, .int_format_string
	jmp .print

.print_fraction:
	mov rdi, .frac_format_string

.print:	
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.int_format_string:
	db "%ld", 0
.frac_format_string:
	db "%ld/%ld", 0

section .text
write_sob_float:
	push rbp
	mov rbp, rsp

	FLOAT_VAL rsi, rsi
	movq xmm0, rsi
	mov rdi, .float_format_string
	mov rax, 1

	;; printf-ing floats (among other things) requires the stack be 16-byte aligned
	;; so align the stack *downwards* (take up some extra space) if needed before
	;; calling printf for floats
	and rsp, -16 
	call printf

	;; move the stack back to the way it was, cause we messed it up in order to
	;; call printf.
	;; Note that the `leave` instruction does exactly this (reset the stack and pop
	;; rbp). The instructions are explicitly layed out here for clarity.
	mov rsp, rbp
	pop rbp
	ret
	
section .data
.float_format_string:
	db "%f", 0		

section .text
write_sob_char:
	push rbp
	mov rbp, rsp

	CHAR_VAL rsi, rsi

	cmp rsi, CHAR_NUL
	je .Lnul

	cmp rsi, CHAR_TAB
	je .Ltab

	cmp rsi, CHAR_NEWLINE
	je .Lnewline

	cmp rsi, CHAR_PAGE
	je .Lpage

	cmp rsi, CHAR_RETURN
	je .Lreturn

	cmp rsi, CHAR_SPACE
	je .Lspace
	jg .Lregular

	mov rdi, .special
	jmp .done	

.Lnul:
	mov rdi, .nul
	jmp .done

.Ltab:
	mov rdi, .tab
	jmp .done

.Lnewline:
	mov rdi, .newline
	jmp .done

.Lpage:
	mov rdi, .page
	jmp .done

.Lreturn:
	mov rdi, .return
	jmp .done

.Lspace:
	mov rdi, .space
	jmp .done

.Lregular:
	mov rdi, .regular
	jmp .done

.done:
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.space:
	db "#\space", 0
.newline:
	db "#\newline", 0
.return:
	db "#\return", 0
.tab:
	db "#\tab", 0
.page:
	db "#\page", 0
.nul:
	db "#\nul", 0
.special:
	db "#\x%02x", 0
.regular:
	db "#\%c", 0

section .text
write_sob_void:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .void
	call printf

	pop rbp
	ret

section .data
.void:
	db "#<void>", 0
	
section .text
write_sob_bool:
	push rbp
	mov rbp, rsp

	cmp word [rsi], word T_BOOL
	je .sobFalse
	
	mov rdi, .true
	jmp .continue

.sobFalse:
	mov rdi, .false

.continue:
	mov rax, 0
	call printf	

	pop rbp
	ret

section .data			
.false:
	db "#f", 0
.true:
	db "#t", 0

section .text
write_sob_nil:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .nil
	call printf

	pop rbp
	ret

section .data
.nil:
	db "()", 0

section .text
write_sob_string:
	push rbp
	mov rbp, rsp

	push rsi

	mov rax, 0
	mov rdi, .double_quote
	call printf
	
	pop rsi

	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rbx, CHAR_TAB
	je .ch_tab
	cmp rbx, CHAR_NEWLINE
	je .ch_newline
	cmp rbx, CHAR_PAGE
	je .ch_page
	cmp rbx, CHAR_RETURN
	je .ch_return
	cmp rbx, CHAR_DOUBLEQUOTE
	je .ch_doublequote
	cmp rbx, CHAR_BACKSLASH
	je .ch_backslash
	cmp rbx, CHAR_SPACE
	jl .ch_hex
	
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx
	jmp .printf
	
.ch_tab:
	mov rdi, .fs_tab
	mov rsi, rbx
	jmp .printf
	
.ch_page:
	mov rdi, .fs_page
	mov rsi, rbx
	jmp .printf
	
.ch_return:
	mov rdi, .fs_return
	mov rsi, rbx
	jmp .printf

.ch_newline:
	mov rdi, .fs_newline
	mov rsi, rbx
	jmp .printf

.ch_doublequote:
	mov rdi, .fs_doublequote
	mov rsi, rbx
	jmp .printf

.ch_backslash:
	mov rdi, .fs_backslash
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	mov rax, 0
	mov rdi, .double_quote
	call printf

	pop rbp
	ret
section .data
.double_quote:
	db CHAR_DOUBLEQUOTE, 0
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	
.fs_tab:
	db "\t", 0
.fs_page:
	db "\f", 0
.fs_return:
	db "\r", 0
.fs_newline:
	db "\n", 0
.fs_doublequote:
	db CHAR_BACKSLASH, CHAR_DOUBLEQUOTE, 0
.fs_backslash:
	db CHAR_BACKSLASH, CHAR_BACKSLASH, 0

section .text
write_sob_pair:
	push rbp
	mov rbp, rsp

	push rsi
	
	mov rax, 0
	mov rdi, .open_paren
	call printf

	mov rsi, [rsp]

	CAR rsi, rsi
	call write_sob

	mov rsi, [rsp]
	CDR rsi, rsi
	call write_sob_pair_on_cdr
	
	add rsp, 1*8
	
	mov rdi, .close_paren
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.open_paren:
	db "(", 0
.close_paren:
	db ")", 0

section .text
write_sob_pair_on_cdr:
	push rbp
	mov rbp, rsp

	mov bl, byte [rsi]
	cmp bl, T_NIL
	je .done
	
	cmp bl, T_PAIR
	je .cdrIsPair
	
	push rsi
	
	mov rax, 0
	mov rdi, .dot
	call printf
	
	pop rsi

	call write_sob
	jmp .done

.cdrIsPair:
	CDR rbx, rsi
	push rbx
	CAR rsi, rsi
	push rsi
	
	mov rax, 0
	mov rdi, .space
	call printf
	
	pop rsi
	call write_sob

	pop rsi
	call write_sob_pair_on_cdr

.done:
	pop rbp
	ret

section .data
.space:
	db " ", 0
.dot:
	db " . ", 0

section .text
write_sob_symbol:
	push rbp
	mov rbp, rsp

	SYMBOL_VAL rsi, rsi
	
	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

	mov rdx, rcx

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rcx, rdx
	jne .ch_simple
	cmp rbx, '+'
	je .ch_hex
	cmp rbx, '-'
	je .ch_hex
	cmp rbx, 'A'
	jl .ch_hex

.ch_simple:
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	pop rbp
	ret
	
section .data
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	

section .text
write_sob_closure:
	push rbp
	mov rbp, rsp

	CLOSURE_CODE rdx, rsi
	CLOSURE_ENV rsi, rsi

	mov rdi, .closure
	mov rax, 0
	call printf

	pop rbp
	ret
section .data
.closure:
	db "#<closure [env:%p, code:%p]>", 0
	;db "#<procedure>", 0

section .text
write_sob_vector:
    push rbp
    mov rbp, rsp

    push rsi

    mov rax, 0
    mov rdi, .vector_open_paren
    call printf

    mov rsi, [rsp]

    SKIP_TYPE_TAG rcx, rsi
    VECTOR_ELEMENTS rax, rsi

.loop:
    cmp rcx, 0
    je .done

    mov rsi, [rax]
    push rax
    push rcx
    call write_sob
    pop rcx
    pop rax

    dec rcx
    jz .done

    push rax
    push rcx
    mov rax, 0
    mov rdi, .vector_space
    call printf
    pop rcx
    pop rax

    add rax, WORD_SIZE
    jmp .loop

.done:
    mov rax, 0
    mov rdi, .vector_close_paren
    call printf

    pop rsi

    pop rbp
    ret

section .data
.vector_open_paren:
    db "#(", 0

.vector_space:
    db " ", 0

.vector_close_paren:
    db ")", 0

section .text
write_sob:
	mov rbx, 0
	mov bl, byte [rsi]	
	jmp qword [.jmp_table + rbx * 8]

section .data
.jmp_table:
	dq write_sob_undefined, write_sob_void, write_sob_nil
	dq write_sob_rational, write_sob_float, write_sob_bool
	dq write_sob_char, write_sob_string, write_sob_symbol
	dq write_sob_closure, write_sob_pair, write_sob_vector

section .text
write_sob_if_not_void:
	mov rsi, rax
	mov bl, byte [rsi]
	cmp bl, T_VOID
	je .continue

	call write_sob
	
	mov rax, 0
	mov rdi, .newline
	call printf
	
.continue:
	ret
section .data
.newline:
	db CHAR_NEWLINE, 0
