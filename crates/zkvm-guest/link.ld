/* Linker script for ZKVM guest programs. */
/* Code at 0x1000, stack at 0xF00000 (set by host CPU). */

ENTRY(_start)

MEMORY {
    RAM (rwx) : ORIGIN = 0x1000, LENGTH = 0xEFF000
}

SECTIONS {
    .text : { *(.text .text.*) } > RAM
    .rodata : ALIGN(4) { *(.rodata .rodata.*) } > RAM
    .data : ALIGN(4) { *(.data .data.*) } > RAM
    .bss : ALIGN(4) {
        __bss_start = .;
        *(.bss .bss.* COMMON)
        __bss_end = .;
    } > RAM

    /DISCARD/ : { *(.eh_frame) *(.comment) *(.debug_*) }
}
