#!/bin/sh
pandoc --toc --standalone --mathjax --metadata title="Judgments As Types" -f markdown -t html README.md -o index.html
