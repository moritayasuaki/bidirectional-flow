pdf :

check :
	agda Everything.agda

pdf :
	agda --latex memo.lagda.tex
	cd latex && xelatex -halt-on-error memo.tex
