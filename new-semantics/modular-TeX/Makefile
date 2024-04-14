TEX = pdflatex
all : main.pdf

main.pdf : main.tex preamble.tex semantics.tex linking.tex cfa.tex
	$(TEX) main.tex

clean :
	rm *.aux *.log *.pdf
