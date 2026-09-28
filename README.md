# Mechanising Denotational Semantics in Agda

Agda code accompanying the **final version** of a paper ([PDF]) [presented] at [MFPS 2026]:

> Peter D. Mosses, Jesper Cockx, Bernhard Reus: *Mechanising Denotational Semantics in Agda*

The [MFPS 2026 – Agda Code] website includes hyperlinked, highlighted listings of the complete code.

[PDF]:                   https://ul-fmf.github.io/mfps-sstt-2026/files/pdfs/mfps/MFPS26-17.pdf
[Presented]:             https://ul-fmf.github.io/mfps-sstt-2026/programme/#wednesday-june-3-mfps
[MFPS 2026]:             https://ul-fmf.github.io/mfps-sstt-2026/mfps/
[MFPS 2026 – Agda Code]: https://pdmosses.github.io/mfps2026-agda/

## Website generation

```sh
cd pages
make check
make web
make serve
```

Browse the generated website [locally](localhost:8026).

## Website deployment

```sh
cd pages
make deploy
```

Browse the generated website [on GitHub Pages](https://pdmosses.github.io/mfps2026-agda/).

## PDF generation

```sh
cd pages
make lagda
make latex
cd latex
pdflatex main
bibtex main
pdflatex main
pdflatex main
```

Browse the generated PDF [in the repository](latex/main.pdf).
(The PDF is not included in the generated website.)

## Repository contents

-   [agda] – Agda code, embedded in Markdown files
-   [latex] – LaTeX and BibTeX  code for generating a PDF
-   [pages] – website generation

    -   [pages/agda-pages] – a Git submodule reference to the [Agda-Pages] repository
    -   [pages/docs]

        -   Markdown source files for non-generated web pages
        -   [.nav.yml] – the navigation configuration file

        [Makefile] – the [Agda-Pages] configuration file
        [properdocs.yml] – the [Properdocs] website build configuration file
        [skip.txt] – a [linkcheck] skip-file
-   [LICENSE] – MIT license
-   [README.md] – this file

## Software dependencies

...

## Contributing

Please report any [issues] that you notice.

Comments and suggestions for improvement are welcome, and can be added as [Discussions].

## Contact

Peter Mosses

[p.d.mosses@tudelft.nl](mailto:p.d.mosses@tudelft.nl)

[pdmosses.github.io](https://pdmosses.github.io)

[Issues]:           issues
[Pull requests]:    pulls
[Discussions]:      discussions

[agda]:             agda
[latex]:            latex
[pages]:            pages
[pages/agda-pages]: pages/agda-pages
[pages/docs]:       pages/docs
[.nav.yml]:         pages/docs/.nav.yml
[Makefile]:         pages/Makefile
[properdocs.yml]:   pages/properdocs.yml
[skip.txt]:         pages/skip.txt
[LICENSE]:          LICENSE.md
[README.md]:        README.md

[Agda-Pages]:       https://github.com/pdmosses/agda-pages/
[linkcheck]:        https://github.com/filiph/linkcheck/
[Properdocs]:       https://properdocs.org