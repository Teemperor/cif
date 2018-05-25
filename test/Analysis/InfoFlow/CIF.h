#ifndef CIF_H
#define CIF_H

#ifdef __clang__

// Place the attributes that Cif can later pick up when scanning the AST.
#define CIFOut __attribute__((annotate("InfoFlow-Out")))
#define CIFLabel(LBL) __attribute__((annotate("InfoFlow|" LBL)))
#define CIFPureList namespace __CIF_Unqiue_Name_Pure
#define CIFPure __attribute__((annotate("InfoFlow-Pure")))

// This special comma operator shouldn't influence the program behavior but
// gives us a way to find back the classify node. The void cast is to make this
// node even more unique and prevent compiler warnings from the unused string
// literal.
#define CIFDeclassify(LBL, EXPR) ((void)LBL, EXPR)

#define CIF

#else // __clang__

// Empty macros because the compiler is not aware of Cif.
#define CIFOut
#define CIFLabel(LBL)
#define CIFPure
#define CIFDeclassify(LBL, EXPR) (EXPR)

#endif // __clang__

#endif // CIF_H
