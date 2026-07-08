GEN=aux fdb_latexmk fls log pdf

all: article.pdf

# .PHONY because deps are (supposed to be) tracked by latexmk
article.pdf: .PHONY article.tex
	latexmk -pdf -pdflatex="pdflatex ${TEXFLAGS} %O %S" article.tex

.PHONY:

clean:
	rm -f $(addprefix article., ${GEN})
