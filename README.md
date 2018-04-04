# Cminus

This is a CMinus compiler made with the Yacc (parsing tool) and the Flex (tokenization). This compiler translate the Cminus language, which is a simpilfication of the C language, to the machine code of my architecture, the ENIL Architecture. I had developed this just using C, and the Yacc and Flex tools.

To run this compiler, just download all the files, paste the C/Cminus code in the file "entrada.txt" and then run the make file. The output will go out in different files:

output.txt - Contains the syntax tree, and the symbol table of the code.

assembly.txt - Contains the assembly code.

CodigoMaquina.txt - Contains the object, binary or machine code for the ENILA. Spefically is formated as a Verilog sequence of memory positions. Please see the documentations of the ENILA architecture.

PS.: READ THE MAKE FILE, I HAD USED THE G++, SO YOU NEED TO INSTALL THE G++ PACKAGE IN YOUR LINUX/UNIX

The techcnical report/ documentation is the file Lucas_Vecchete_RelatorioFinal.pdf. This report is in portuguese, I promise that sometime I will write an english report.

For more information, contact me:

Linkedin: linkedin.com/in/vecchete
Email: lucasvecchete@hotmail.com

