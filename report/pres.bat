@echo off

lhs2tex --poly -o presentation.tmp.tex presentation.tex
latex -interaction=batchmode -job-name=presentation -interaction=batchmode presentation.tmp.tex
pdflatex -interaction=batchmode -job-name=presentation -interaction=batchmode presentation.tmp.tex