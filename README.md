# AutoBlueprint

This is a tool for automatically creating a `content.tex` file to be used by leanblueprint.

## Usage

* Add this package as a dependency to your project.
* Run the commands `lake update AutoBlueprint` and `lake build` from a terminal inside your project folder.
* Import the `AutoBlueprint` module in the root file of your project.
* Run the command `#eval createBlueprint "your_content.tex"` in the root file of your project.
* `your_content.tex` file is ready.

## Features

* The tex file contains a theorem and a proof environment for each theorem-like statement.
* The tex file contains a definition and a proof environment for each definition-like statement.
* `\uses` commands for each environment are automatically handled.
* `\leanname` commands for non-proof environments are automatically handled.
* Labels of non-proof environments are the same as their Lean names.

## Non-Features

* Autoblueprint assumes that the project is sorry-free therefore all environments contains the `\leanok` command.
* The created Latex environments does not contain visible content.

## TODO

* Detect declarations using `sorry` and do not put `\leanok` command into their environments.
* Get the visible content of the latex environments from the docstrings of the declarations.
