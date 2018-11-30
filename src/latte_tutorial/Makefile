
MARKDOWNIZE_PATH = ../../../markdownize
PYTHON = python3

MARKDOWNIZE = $(PYTHON) $(MARKDOWNIZE_PATH)/markdownize.py

MFLAGS = --begin ";;{" --end ";;}" --lang "clojure" --remove-prefix ";;"

OBJS = ch00_front_matter.clj.md

all: markdownize

markdownize: $(OBJS)

%.clj.md : %.clj
	$(MARKDOWNIZE) --input $< --output $@ $(MFLAGS)

clean:
	rm -f *~
	rm -f *.md



