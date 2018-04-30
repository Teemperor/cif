#ifndef CIF_H
#define CIF_H

#define CIFLabel(LBL) __attribute__((annotate("InfoFlow|" LBL)))

#define CIFPure namespace __CIF_Unqiue_Name_Pure

#define CIFDeclassify(LBL, EXPR) ((void)LBL, EXPR)

#endif // CIF_H
