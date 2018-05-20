#ifndef CIF_H
#define CIF_H

#ifdef __clang__

#define CIFOut __attribute__((annotate("InfoFlow-Out")))
#define CIFLabel(LBL) __attribute__((annotate("InfoFlow|" LBL)))
#define CIFPureList namespace __CIF_Unqiue_Name_Pure
#define CIFPure __attribute__((annotate("InfoFlow-Pure")))
#define CIFDeclassify(LBL, EXPR) ((void)LBL, EXPR)

#define CIF

#else // __clang__

#define CIFOut
#define CIFLabel(LBL)
#define CIFPure
#define CIFDeclassify(LBL, EXPR) (EXPR)

#endif // __clang__

#endif // CIF_H
