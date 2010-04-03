lhs2tex --poly report.tex -o report.tmp.tex report.tex
latex -interaction=batchmode -job-name=report -interaction=batchmode report.tmp.tex
pdflatex -interaction=batchmode -job-name=report -interaction=batchmode report.tmp.tex