# AutoBlueprint

This is a tool for automatically creating a `content.tex` file to be used by leanblueprint.

## Usage

* Add this package as a dependency to your project.
* Run the commands `lake update AutoBlueprint` and `lake build` from your terminal inside your project folder.
* Import the `AutoBlueprint` module in the root file of your project.
* Run the command `#eval createBlueprint your_content.tex` in the root file of your project.
* `your_content.tex` file is ready.

## Features

* The tex file contains a theorem environment and a proof environment for each theorem-like statement.
* The tex file contains a definition environment and a proof environment for each definition-like statement.
* Non-proof environments contains the `\label`, `\leanname`, `\leanok`, `\uses` commands.
* Proof environments contains the `\leanok`, `\uses` commands.

## Non-Features

* The created Latex environments does not contain anything other than `\label`, `\leanname`, `\leanok`, `\uses` commands i.e. no visible content.
* `\label`s are the same as the `\leanname`s.
* `\leanok` command is always present.

## TODO

* Detect declarations using `sorry` and do not put `\leanok` command into their environments.
* Get the visible content of the latex environments from the docstrings of the declarations.
