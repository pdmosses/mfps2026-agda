# Mechanising Denotational Semantics in Agda

Agda code accompanying the **final version** of a paper [presented] at [MFPS 2026]:

> Peter D. Mosses, Jesper Cockx, Bernhard Reus: *Mechanising Denotational Semantics in Agda*

The [MFPS 2026 – Agda Code] website includes hyperlinked, highlighted listings of the complete code.


> [!TIP]
> The Agda code presented in the **preliminary version** of the paper ([PDF])
> is available in the `preliminary` branch of this repository.
> A build of the [preliminary website] generated from it has been added as a
> subdirectory of the [MFPS 2026 – Agda Code] website.
 
[PDF]:                   https://ul-fmf.github.io/mfps-sstt-2026/files/pdfs/mfps/MFPS26-17.pdf
[Presented]:             https://ul-fmf.github.io/mfps-sstt-2026/programme/#wednesday-june-3-mfps
[MFPS 2026]:             https://ul-fmf.github.io/mfps-sstt-2026/mfps/
[Preliminary website]:   https://pdmosses.github.io/mfps2026-agda/preliminary/
[MFPS 2026 – Agda Code]: https://pdmosses.github.io/mfps2026-agda/

## Website generation

```sh
cd pages
make check
make web
make serve
```

You can then browse the generated website [locally](http://localhost:8026/mfps2026-agda/).

## Website deployment

```sh
cd pages
make check
make web
make deploy
```

You can then browse the generated website [on GitHub Pages](https://pdmosses.github.io/mfps2026-agda/).

## Repository contents

-   [agda] – Agda code, embedded in Markdown files
-   [pages] – website generation using [Agda-Pages]

    -   [pages/agda-pages] – a Git submodule reference to the [Agda-Pages] repository
    -   [pages/docs]

        -   Non-generated Markdown source files
        -   [preliminary] – a build of the preliminary website
        -   [.nav.yml] – the navigation configuration file

        [Makefile] – the [Agda-Pages] configuration file
        [properdocs.yml] – the [Properdocs] website build configuration file
        [skip.txt] – a [linkcheck] skip-file
-   [LICENSE] – MIT license
-   [README.md] – this file

## Installation

After cloning the repository for the first time, initialise the submodule at `pages/agda-pages`
by running the following command in the repository root:

```sh
git submodule update --init --recursive
```

To update the submodule to a subsequent commit, run:

```sh
git submodule update --remote
```

> [!WARNING]
> The submodule currently references a commit of the unstable `dev` branch of `agda-pages`.
> This may change.

## Software dependencies

See the relevant branch of the [Agda-Pages] repository.

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
[preliminary]:      pages/docs/preliminary
[.nav.yml]:         pages/docs/.nav.yml
[Makefile]:         pages/Makefile
[properdocs.yml]:   pages/properdocs.yml
[skip.txt]:         pages/skip.txt
[LICENSE]:          LICENSE.md
[README.md]:        README.md

[Agda-Pages]:       https://github.com/pdmosses/agda-pages/
[linkcheck]:        https://github.com/filiph/linkcheck/
[Properdocs]:       https://properdocs.org