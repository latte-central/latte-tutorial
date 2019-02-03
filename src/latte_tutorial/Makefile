
MARKDOWNIZE_PATH = ../../../markdownize
PYTHON = python3

MARKDOWNIZE = $(PYTHON) $(MARKDOWNIZE_PATH)/markdownize.py
MFLAGS = --begin ";;{" --end ";;}" --lang "clojure" --remove-prefix ";; "

PANDOC = pandoc
HIGHLIGHT_STYLE = tango # tango pygments espresso zenburn kate monochrome breezeda

PANDOC_FLAGS = -s --toc --pdf-engine=xelatex --metadata-file=book.yaml --highlight-style=$(HIGHLIGHT_STYLE)


HEADER = header.md

OBJS = ch01_front_matter.clj.md ch02_first_steps.clj.md ch03_game_rules.clj.md ch04_logic_bits.clj.md ch05_set_theory.clj.md

all: markdownize

markdownize: $(OBJS)

%.clj.md : %.clj
	$(MARKDOWNIZE) --input $< --output $@ $(MFLAGS)

pdf: $(OBJS)
	$(PANDOC) $(PANDOC_FLAGS) -o latte-tutorial.pdf $(OBJS) 

tex: $(OBJS)
	$(PANDOC) $(PANDOC_FLAGS) -o latte-tutorial.tex $(OBJS) 

clean:
	rm -fv *~
	rm -fv *.md
	rm -fv *.aux
	rm -fv *.log




