.PHONY: clean html

html: src/Quotient.lagda.md
	agda --html --html-highlight=code src/Quotient.lagda.md
	pandoc html/Quotient.md -o html/Quotient.html

clean:
	rm -rf html/ src/*.agdai
