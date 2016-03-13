;; tiny 32bit PE assembler (windows) -- aurelien.aptel@gmail.com
;; -*- indent-tabs-mode: nil -*-

(require 'pcase)
(require 'cl)

(defvar ec-registers '(eax ecx edx ebx esp ebp esi edi))

(defun ec-register-p (x)
  (and (symbolp x) (memq x ec-registers)))

(defun ec-register-val (r)
  (position r ec-registers))

(defun ec-encode (inst)
  (pcase inst
    ;; add REG, INT32
    (`(add ,(and dst (pred ec-register-p)) ,(and src (pred integerp)))
     `(#b10000001
       ,(+ #b11000000 (ec-register-val dst))
       ,@(ec-u32 src)))

    ;; add REG, REG
    (`(add ,(and dst (pred ec-register-p)) ,(and src (pred ec-register-p)))
     (list #b00000001
           (logior #b11000000 (lsh (ec-register-val src) 3) (ec-register-val dst))))

    ;; add REG, [REG]
    (`(add ,(and dst (pred ec-register-p)) ( ,(and src (pred ec-register-p)) ))
     (list #b00000011
           (logior #b00000000 (lsh (ec-register-val dst) 3) (ec-register-val src))))

    ;; mov REG, INT32
    (`(mov ,(and dst (pred ec-register-p)) ,(and src (pred integerp)))
     `(,(+ #b10111000 (ec-register-val dst))
       ,@(ec-u32 src)))

    ;; mov REG, REG
    (`(mov ,(and dst (pred ec-register-p)) ,(and src (pred ec-register-p)))
     (list #b10001001
           (logior #b11000000 (lsh (ec-register-val src) 3) (ec-register-val dst))))

    ;; mov REG, [REG]
    (`(mov ,(and dst (pred ec-register-p)) (,(and src (pred ec-register-p))))
     (list #b10001011
           (logior #b00000000 (lsh (ec-register-val dst) 3) (ec-register-val src))))

    ;; mov [REG], REG
    (`(mov (,(and dst (pred ec-register-p))) ,(and src (pred ec-register-p)))
     (list #b10001001
           (logior #b00000000 (lsh (ec-register-val src) 3) (ec-register-val dst))))

    ;; nop
    ((or `nop `(nop))
     (list #x90))

    ;; inc REG
    (`(inc  ,(and reg (pred ec-register-p)))
     (list (+ #b01000000 (ec-register-val reg))))

    ;; inc [REG]
    (`(inc  (,(and reg (pred ec-register-p))))
     (list #xff (ec-register-val reg)))

    ;; dec REG
    (`(dec  ,(and reg (pred ec-register-p)))
     (list (+ #x48 (ec-register-val reg))))

    ;; dec [REG]
    (`(dec  (,(and reg (pred ec-register-p))))
     (list #xff (+ #x08 (ec-register-val reg))))

    ;; push REG
    (`(push  ,(and reg (pred ec-register-p)))
     (list (+ #x50 (ec-register-val reg))))

    ;; push [REG]
    (`(push  (,(and reg (pred ec-register-p))))
     (list #xff (+ #x30 (ec-register-val reg))))

    ;; pop REG
    (`(pop  ,(and reg (pred ec-register-p)))
     (list (+ #x58 (ec-register-val reg))))

    ;; pop [REG]
    (`(pop  (,(and reg (pred ec-register-p))))
     (list #x8f (ec-register-val reg)))

    (_
     (error "unhandled instruction %S" inst))))

(defun ec-align-to (value align)
  (let ((r (mod value align)))
    (if (= r 0)
        value
      (+ value (- align r)))))

(defun ec-u8 (v)
  "Return V as a 8 bit list of 1 byte"
  (when (stringp v) (setq v (elt v 0)))
  (list (logand v #xff)))

(defun ec-u16 (v)
  "Return V as a 16 bit little-endian list of bytes"
  (setq v (logand v #xffff))
  (list (logand v #xff) (lsh (logand v #xff00) -8)))

(defun ec-u32 (v)
  "Return V as a 32 bit little-endian list of bytes"
  ;; 32-bit emacs has to store 0xffffffff as a double so deal with
  ;; that first
  (setq v (mod v #x100000000))
  (let ((hi (truncate (/ v (expt 2 16))))
        (lo (truncate (mod v #x10000))))
    (list (logand lo #xff) (lsh (logand lo #xff00) -8)
          (logand hi #xff) (lsh (logand hi #xff00) -8))))

(defun ec-str (str max)
  (list
   (if (> (length str) max)
       (substring str 0 max)
     (concat str (make-string (- max (length str)) 0)))))

(defun ec-to-string (xs)
  (mapconcat (lambda (x) (format "%02x" x)) xs " "))

(defun ec-seek (offset)
  (setq offset (1+ offset))
  (if (>= offset (point-max))
      (insert (make-string (- offset (point-max)) 0))
    (error "buffer already bigger (pmax=%S, offset=%S)" (point-max) offset)
    (goto-char offset)))


(defun ec-write-pe (prog-data prog-code file)
  (let* ((dos-hdr-size #x40)
         (dos-stub-size (+ dos-hdr-size (length ec-dos-prog)))
         (pe-offset (ec-align-to dos-stub-size 8))

         (nb-sections 4)

         (pe-sig-size   #x4)
         (coff-hdr-size #x14)
         (opt-hdr-size  #xe0)
         (pe-hdr-size   (+ pe-sig-size coff-hdr-size opt-hdr-size))
         (sec-hdr-size  #x28)

         (iat-entry-size               #x4)
         (import-dir-entry-size        #x14)
         (import-lookup-tbl-entry-size iat-entry-size)
         (name-table-entry-size        #x12)

         (image-base #x00400000)
         (sec-align  #x1000)
         (file-align #x200)


         (headers-size (+ pe-offset pe-hdr-size (* nb-sections sec-hdr-size)))

         (text-rva (ec-align-to headers-size sec-align))
         (text-offset (ec-align-to headers-size file-align))
         (text-size (length prog-code))

         (rdata-rva (ec-align-to (+ text-rva text-size) sec-align))
         (rdata-offset (ec-align-to (+ text-offset text-size) file-align))
         (rdata-size (length prog-data))

         (idata-rva (ec-align-to (+ rdata-rva rdata-size) sec-align))
         (idata-offset (ec-align-to (+ rdata-offset rdata-size) file-align))

         (num-imports 4)
         (iat-rva idata-rva)
         (iat-size (* (1+ num-imports) iat-entry-size))
         (import-dir-table-rva  (+ iat-rva iat-size))
         (import-dir-table-size (* 2 import-dir-entry-size))
         (import-lookup-table-rva (+ import-dir-table-rva import-dir-table-size))

         (name-table-rva (+ import-lookup-table-rva (* (1+ num-imports) import-lookup-tbl-entry-size)))
         (dll-name-rva (+ name-table-rva (* num-imports name-table-entry-size)))

         (name-table-size (+ (* num-imports name-table-entry-size) 16))
         (idata-size (+ name-table-rva (- name-table-size idata-rva)))

         (bss-rva (ec-align-to (+ idata-rva idata-size) sec-align))
         (bss-size 4096)
         )

    (with-temp-buffer
      (set-buffer-multibyte nil)

      ;; mz header
      (mapcar
       'insert
       (append
        '("MZ")                                  ; magic
        (ec-u16 (mod dos-stub-size 512))         ; last page size
        (ec-u16 (/ (ec-align-to dos-stub-size 512) 512)) ; pages in file
        (ec-u16 0)                               ; relocation
        (ec-u16 (/ dos-hdr-size 16))             ; size of header in paragraphs
        (ec-u16 0)                               ; min extra paragraphs needed
        (ec-u16 1)                               ; max extra paragraphs needed
        (ec-u16 0)                               ; initial (relative) ss value
        (ec-u16 0)                               ; initial sp value
        (ec-u16 0)                               ; checksum
        (ec-u16 0)                               ; initial ip value
        (ec-u16 0)                               ; initial (relative) cs value
        (ec-u16 dos-hdr-size)                    ; file address of relocation table
        (ec-u16 0)                               ; overlay number
        (ec-u16 0)                               ; reserved0
        (ec-u16 0)                               ; reserved1
        (ec-u16 0)                               ; reserved2
        (ec-u16 0)                               ; reserved3
        (ec-u16 0)                               ; oem id
        (ec-u16 0)                               ; oem info
        (make-list (* 2 10) #x00)                ; reserved (10x zero 16b-words)
        (ec-u32 pe-offset)                       ; file offset of pe header
        ec-dos-prog))

      (ec-seek pe-offset)

      ;; pe signature
      (mapcar
       'insert
       (append
        '("PE")
        (ec-u8 0)
        (ec-u8 0)))

      ;; coff header
      (mapcar
       'insert
       (append
        (ec-u16 #x14c)       ; Machine = IMAGE_FILE_MACHINE_I386
        (ec-u16 nb-sections) ; NumberOfSections
        (ec-u32 0)           ; TimeDateStamp
        (ec-u32 0)           ; PointerToSymbolTable
        (ec-u32 0)           ; NumberOfSymbols
        (ec-u16 opt-hdr-size); SizeOfOptionalHeader
        (ec-u16 #x103)       ; Characteristics = no reloc, exec, 32b
        ))

      (mapcar
       'insert
       (append
        ;; Optional header, part 1: standard fields
        (ec-u16 #x10b)                                            ; Magic: PE32
        (ec-u8 0)                                                 ; MajorLinkerVersion
        (ec-u8 0)                                                 ; MinorLinkerVersion
        (ec-u32 text-size)                                        ; SizeOfCode
        (ec-u32 (+ rdata-size idata-size))                        ; SizeOfInitializedData
        (ec-u32 bss-size)                                         ; SizeOfUninitializedData
        (ec-u32 text-rva)                                         ; AddressOfEntryPoint
        (ec-u32 text-rva)                                         ; BaseOfCode
        (ec-u32 rdata-rva)                                        ; BaseOfData

        ;; Optional header, part 2: Windows-specific fields
        (ec-u32 image-base)                                       ; ImageBase
        (ec-u32 sec-align)                                        ; SectionAlignment
        (ec-u32 file-align)                                       ; FileAlignment
        (ec-u16 3)                                                ; MajorOperatingSystemVersion
        (ec-u16 10)                                               ; MinorOperatingSystemVersion
        (ec-u16 0)                                                ; MajorImageVersion
        (ec-u16 0)                                                ; MinorImageVersion
        (ec-u16 3)                                                ; MajorSubsystemVersion
        (ec-u16 10)                                               ; MinorSubsystemVersion
        (ec-u32 0)                                                ; Win32VersionValue
        (ec-u32 (ec-align-to (+ bss-rva bss-size) sec-align))     ; SizeOfImage
        (ec-u32 (ec-align-to (+ headers-size) file-align))        ; SizeOfHeaders
        (ec-u32 0)                                                ; Checksum
        (ec-u16 3)                                                ; Subsystem: Console
        (ec-u16 0)                                                ; DllCharacteristics
        (ec-u32 #x100000)                                         ; SizeOfStackReserve
        (ec-u32 #x1000)                                           ; SizeOfStackCommit
        (ec-u32 #x100000)                                         ; SizeOfHeapReserve
        (ec-u32 #x1000)                                           ; SizeOfHeapCommit
        (ec-u32 0)                                                ; LoadFlags
        (ec-u32 16)                                               ; NumberOfRvaAndSizes

        ;; Optional header, part 3: data directories.
        (ec-u32 0) (ec-u32 0)                                     ; Export Table.
        (ec-u32 import-dir-table-rva)                             ; Import Table.
        (ec-u32 import-dir-table-size)
        (ec-u32 0) (ec-u32 0)                                     ; Resource Table.
        (ec-u32 0) (ec-u32 0)                                     ; Exception Table.
        (ec-u32 0) (ec-u32 0)                                     ; Certificate Table.
        (ec-u32 0) (ec-u32 0)                                     ; Base Relocation Table.
        (ec-u32 0) (ec-u32 0)                                     ; Debug.
        (ec-u32 0) (ec-u32 0)                                     ; Architecture.
        (ec-u32 0) (ec-u32 0)                                     ; Global Ptr.
        (ec-u32 0) (ec-u32 0)                                     ; TLS Table.
        (ec-u32 0) (ec-u32 0)                                     ; Load Config Table.
        (ec-u32 0) (ec-u32 0)                                     ; Bound Import.
        (ec-u32 iat-rva)                                          ; Import Address Table.
        (ec-u32 iat-size)
        (ec-u32 0) (ec-u32 0)                                     ; Delay Import Descriptor.
        (ec-u32 0) (ec-u32 0)                                     ; CLR Runtime Header.
        (ec-u32 0) (ec-u32 0)                                     ; (Reserved).

        ;; Section header #1: .text
        (ec-str ".text" 8)                                        ; Name
        (ec-u32 text-size)                                        ; VirtualSize
        (ec-u32 text-rva)                                         ; VirtualAddress
        (ec-u32 (ec-align-to text-size file-align))               ; SizeOfRawData
        (ec-u32 text-offset)                                      ; PointerToRawData
        (ec-u32 0)                                                ; PointerToRelocations
        (ec-u32 0)                                                ; PointerToLinenumbers
        (ec-u16 0)                                                ; NumberOfRelocations
        (ec-u16 0)                                                ; NumberOfLinenumbers
        (ec-u32 #x60000020)                                       ; Characteristics: code, read, execute

        ;; Section header #2: .rdata
        (ec-str ".rdata" 8)                                       ; Name
        (ec-u32 rdata-size)                                       ; VirtualSize
        (ec-u32 rdata-rva)                                        ; VirtualAddress
        (ec-u32 (ec-align-to rdata-size file-align))              ; SizeOfRawData
        (ec-u32 rdata-offset)                                     ; PointerToRawData
        (ec-u32 0)                                                ; PointerToRelocations
        (ec-u32 0)                                                ; PointerToLinenumbers
        (ec-u16 0)                                                ; NumberOfRelocations
        (ec-u16 0)                                                ; NumberOfLinenumbers
        (ec-u32 #x40000040)                                       ; Characteristics: data, read

        ;; Section header #3: .idata
        (ec-str ".idata" 8)                                       ; Name
        (ec-u32 idata-size)                                       ; VirtualSize
        (ec-u32 idata-rva)                                        ; VirtualAddress
        (ec-u32 (ec-align-to idata-size file-align))              ; SizeOfRawData
        (ec-u32 idata-offset)                                     ; PointerToRawData
        (ec-u32 0)                                                ; PointerToRelocations
        (ec-u32 0)                                                ; PointerToLinenumbers
        (ec-u16 0)                                                ; NumberOfRelocations
        (ec-u16 0)                                                ; NumberOfLinenumbers
        (ec-u32 #xc0000040)                                       ; Characteristics: data, read, write

        ;; Section header #4: .bss
        (ec-str ".bss" 8)                                         ; Name
        (ec-u32 bss-size)                                         ; VirtualSize
        (ec-u32 bss-rva)                                          ; VirtualAddress
        (ec-u32 0)                                                ; SizeOfRawData
        (ec-u32 0)                                                ; PointerToRawData
        (ec-u32 0)                                                ; PointerToRelocations
        (ec-u32 0)                                                ; PointerToLinenumbers
        (ec-u16 0)                                                ; NumberOfRelocations
        (ec-u16 0)                                                ; NumberOfLinenumbers
        (ec-u32 #xc0000080)                                       ; Characteristics: uninit. data, read, write
        ))

       ;; Write .text segment.
      (ec-seek text-offset)
      (mapcar 'insert prog-code)

       ;; Write .rdata segment.
      (ec-seek rdata-offset)
      (mapcar 'insert prog-data)

       ;; Write .idata segment.
      (ec-seek idata-offset)

       ;; Import Address Table (IAT):
       ;; (Same as the Import Lookup Table)
      (mapcar
       'insert
       (append
        (ec-u32 (+ name-table-rva (* 0 name-table-entry-size)))
        (ec-u32 (+ name-table-rva (* 1 name-table-entry-size)))
        (ec-u32 (+ name-table-rva (* 2 name-table-entry-size)))
        (ec-u32 (+ name-table-rva (* 3 name-table-entry-size)))
        (ec-u32 0)

        ;; Import Directory Table
        ;; kernel32.dll
        (ec-u32 import-lookup-table-rva)                          ; ILT RVA
        (ec-u32 0)                                                ; Time/Data Stamp
        (ec-u32 0)                                                ; Forwarder Chain
        (ec-u32 dll-name-rva)                                     ; Name RVA
        (ec-u32 iat-rva)                                          ; Import Address Table RVA
        ;; Null terminator
        (ec-u32 0)
        (ec-u32 0)
        (ec-u32 0)
        (ec-u32 0)
        (ec-u32 0)

        ;; Import Lookup Table
        (ec-u32 (+ name-table-rva (* 0 name-table-entry-size)))   ; GetStdHandle
        (ec-u32 (+ name-table-rva (* 1 name-table-entry-size)))   ; ReadFile
        (ec-u32 (+ name-table-rva (* 2 name-table-entry-size)))   ; WriteFile
        (ec-u32 (+ name-table-rva (* 3 name-table-entry-size)))   ; ExitProcess
        (ec-u32 0)                                                ; Null terminator

        ;; Hint/Name Table
        (ec-u16 0)                                                ; Hint
        (ec-str "GetStdHandle" 16)                                ; Name
        (ec-u16 0)                                                ; Hint
        (ec-str "ReadFile" 16)                                    ; Name
        (ec-u16 0)                                                ; Hint
        (ec-str "WriteFile" 16)                                   ; Name
        (ec-u16 0)                                                ; Hint
        (ec-str "ExitProcess" 16)                                 ; Name
        ;; Put the dll name here too; we've got to write it somewhere.
        (ec-str "kernel32.dll" 16)
        ))
      (let ((coding-system-for-write 'raw-text-unix))
        (write-file file)))))

(defun ec-write-bin (file content)
  (with-temp-buffer
    (set-buffer-multibyte nil)
    (mapc 'insert content)
    (let ((coding-system-for-write 'raw-text-unix))
      (write-file file))))

(defun ec-main ()
  (ec-write-pe ec-prog-data ec-prog-code "rot13.exe"))

(defun ec-to-bin (n &optional pad)
  (when (not pad)
    (setq pad 32))
  (let ((tab ["0000" "0001" "0010" "0011" "0100" "0101" "0110" "0111"
	      "1000" "1001" "1010" "1011" "1100" "1101" "1110" "1111"])
	(res "")
	(i 0))
    (while (< i pad)
      (setq res (concat (aref tab (logand n #xf))
                        (if (and (not (zerop i)) (zerop (mod i 8))) " " "")
                        res))
      (setq n (lsh n -4))
      (incf i 4))
    res))

(defun ec-nasm (src)
  (let* ((bin-file "/tmp/nasm-src-tmp")
	 (src-file (concat bin-file ".asm")))
    (with-temp-file src-file
      (insert src))
    (shell-command-to-string (concat "rm -f " bin-file " && nasm -o " bin-file " " src-file))
    (with-temp-buffer
      (set-buffer-multibyte nil)
      (let ((coding-system-for-read 'raw-text-unix))
	(insert-file-contents bin-file))
      ;; convert to buffer string to list. this seems needlessly complex but oh well...
      (let (r)
	(mapc (lambda (c) (push c r)) (buffer-string))
	(nreverse r)))))

(defun ec-ndisasm (bin)
  (let* ((bin-file "/tmp/nasm-src-tmp"))
    (ec-write-bin bin-file bin)
    (shell-command-to-string (concat "ndisasm -b 32 " bin-file))))

(defvar ec-dos-prog
  (list #x8c #xc8                  ;  mov    %cs,%ax
        #x8e #xd8                  ;  mov    %ax,%ds
        #xba #x10 #x00             ;  mov    $16,%dx
        #xb4 #x09                  ;  mov    $0x9,%ah
        #xcd #x21                  ;  int    $0x21
        #xb8 #x01 #x4c             ;  mov    $0x4c01,%ax
        #xcd #x21                  ;  int    $0x21
        "H" "e" "l" "l" "o" ","    ;  ($-terminated string)
        " " "D" "O" "S" " " "w"
        "o" "r" "l" "d" "!" "$"))

(defvar ec-prog-code
  (list
   #x6a #xf6                      ;   pushl  $-10
   #xff #x15 #x00 #x30 #x40 #x00  ;   call   *iat_slot0
   #x89 #xc6                      ;   movl   %eax,%esi
   #x6a #xf5                      ;   pushl  $-11
   #xff #x15 #x00 #x30 #x40 #x00  ;   call   *iat_slot0
   #x89 #xc7                      ;   movl   %eax,%edi
                                  ; read:
   #x6a #x00                      ;   pushl  $0
   #x89 #xe0                      ;   movl   %esp,%eax
   #x6a #x00                      ;   pushl  $0
   #x50                           ;   pushl  %eax
   #x68 #x00 #x10 #x00 #x00       ;   pushl  $4096
   #x68 #x00 #x40 #x40 #x00       ;   pushl  $buffer
   #x56                           ;   pushl  %esi
   #xff #x15 #x04 #x30 #x40 #x00  ;   call   *iat_slot1
   #x58                           ;   popl   %eax
   #x85 #xc0                      ;   testl  %eax,%eax
   #x7e #x26                      ;   jle    end
   #xb9 #x00 #x40 #x40 #x00       ;   movl   $buffer,%ecx
   #x89 #xc2                      ;   movl   %eax,%edx
                                  ; rot13:
   #x0f #xb6 #x19                 ;   movzbl (%ecx),%ebx
   #x8a #x9b #x00 #x20 #x40 #x00  ;   movb   rot13_table(%ebx),%bl
   #x88 #x19                      ;   movb   %bl,(%ecx)
   #x41                           ;   incl   %ecx
   #x48                           ;   decl   %eax
   #x75 #xf1                      ;   jnz    rot13
   #x29 #xd1                      ;   subl   %edx,%ecx
   #x6a #x00                      ;   pushl  $0
   #x54                           ;   pushl  %esp
   #x52                           ;   pushl  %edx
   #x51                           ;   pushl  %ecx
   #x57                           ;   pushl  %edi
   #xff #x15 #x08 #x30 #x40 #x00  ;   call   *iat_slot2
   #xeb #xbd                      ;   jmp    read
                                  ; end:
   #x6a #x00                      ;   pushl  $0
   #xff #x15 #x0c #x30 #x40 #x00  ;   call   *iat_slot3
   ))

(defvar ec-prog-data
  (list
   0   1   2   3   4   5   6
   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21  22
   23  24  25  26  27  28  29  30  31  32  33  34  35  36  37  38
   39  40  41  42  43  44  45  46  47  48  49  50  51  52  53  54
   55  56  57  58  59  60  61  62  63  64 "N" "O" "P" "Q" "R" "S"
   "T" "U" "V" "W" "X" "Y" "Z" "A" "B" "C" "D" "E" "F" "G" "H" "I"
   "J" "K" "L" "M"  91  92  93  94  95  96 "n" "o" "p" "q" "r" "s"
   "t" "u" "v" "w" "x" "y" "z" "a" "b" "c" "d" "e" "f" "g" "h" "i"
   "j" "k" "l" "m" 123 124 125 126 127 128 129 130 131 132 133 134
   135 136 137 138 139 140 141 142 143 144 145 146 147 148 149 150
   151 152 153 154 155 156 157 158 159 160 161 162 163 164 165 166
   167 168 169 170 171 172 173 174 175 176 177 178 179 180 181 182
   183 184 185 186 187 188 189 190 191 192 193 194 195 196 197 198
   199 200 201 202 203 204 205 206 207 208 209 210 211 212 213 214
   215 216 217 218 219 220 221 222 223 224 225 226 227 228 229 230
   231 232 233 234 235 236 237 238 239 240 241 242 243 244 245 246
   247 248 249 250 251 252 253 254 255))
