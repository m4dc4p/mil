lhs2tex --poly -o %~n1.f.tex %1
pdflatex -interaction=batchmode -jobname="%~n1" %~n1.f.tex
pdflatex -interaction=batchmode -jobname="%~n1" %~n1.f.tex
