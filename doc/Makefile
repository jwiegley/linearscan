all: linearscan.pdf

linearscan.v.tex: linearscan.tex
	coq-tex -v -image ./lscoqtop $? > /tmp/out 2>&1
	(grep -q Error /tmp/out && cat /tmp/out && rm -f /tmp/out && exit 1) || exit 0
	@rm -f /tmp/out

linearscan.pdf: linearscan.v.tex
	pdflatex $?
	pdflatex $? > /dev/null 2>&1
	pdflatex $? > /dev/null 2>&1
	mv linearscan.v.pdf $@

clean:
	rm *.v.*
