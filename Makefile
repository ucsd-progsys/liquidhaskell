
tags:
	hasktags -c src/
	hasktags -e src/
	hasktags -x -c src/

ghcid:
	stack exec -- ghcid --command="stack ghci --ghci-options=-fno-code"