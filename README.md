# Simply Typed Lambda Calculus (STLC) in Agda

This is the code for a short tutorial on how to write a tag-less STLC
interpreter in the dependently typed functional programming language
[Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.HomePage).
It was presented at the [FunFR functional programming meetup](http://www.meetup.com/Freiburg-Functional-Programming-Meetup/events/190956772/) on
2014-06-28. An alternative tutorial with similar scope can be found
[here](http://gergo.erdi.hu/blog/2013-05-01-simply_typed_lambda_calculus_in_agda,_without_shortcuts/).

A tag-less interpreter safely omits checking run-time type tags during
evaluation by relying on an expression datatype that guarantees that
all expressions are well-typed by construction. 

There is currently no real documentation in the code. Hopefully there
will be some soon. In the meantime, you are encouraged to open issues
with questions, or send pull-requests :)

## Content

- `STLC-tagless.agda`: code of the tag-less interpreter. There are
  three version:
  - `STLC.Try1`: a version without variables to demonstrate the principles.
  - `STCL.Try2`: a complete tag-less version
  - `STCL.Try3`: an alternative to `Try2` with a slightly different
    way to represent variables

  Also there are some typechecking functions that turn untyped
  expressions into typed ones. These modules were not discussed at the
  meeting and might be hard to understand with the current (lack of)
  documentation.
  - `Typeof` : unverified implementation.
  - `Typeof-Precise` : verified implementation.

- `STLC-tagged.hs`: a "tag-full" version written in Haskell, for
  comparison.
 
## Setup

The code was tested with Agda-2.3.2.2 but should also work with newer
versions. The official installation instructions are
[here](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download)
requires the
[standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary)
which you might have to install manually. For that, download and
unpack it into your project directory and add the src folder to Agda's
load path. You can do this in emacs by customizing the variable
agda2-include-dirs.


