;;; Directory Local Variables
;;; See Info node `(emacs) Directory Variables' for more information.

((nil
  (eval setq default-directory
        (locate-dominating-file buffer-file-name ".dir-locals.el")))
 (haskell-mode
  (eval setq flycheck-haskell-options
        (append
         flycheck-haskell-options
         (list
          (concat "-i"
                  (car
                   (file-expand-wildcards "dist/dist-sandbox*/build/autogen")))
          )))))



