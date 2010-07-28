lhs2tex --poly -o %~n1.f.tex %1
pdflatex -interaction=batchmode -job-name="%~n1" %~n1.f.tex