;;; liquid-tip.el --- show inferred liquid-types

;; Copyright (C) 2014 by Ranjit Jhala 

;; Author: Ranjit Jhala <jhala@cs.ucsd.edu>
;; Version: 0.0.1
;; Package-Requires: ((flycheck "0.13") (dash "1.2") (emacs "24.1") (pos-tip "0.5.0"))
;;; License:
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;; see https://github.com/ucsd-progsys/liquidhaskell#emacs

;;; Code:
(eval-when-compile (require 'cl))
(require 'auto-complete)
(require 'json-mode)
(require 'json)
(require 'ring)
(require 'etags)
;; (require 'flymake)
;; (require 'eldoc)
(require 'pos-tip nil t)
;; (require 'log4e)
;; (require 'yaxception)
(require 'thingatpt)
(require 'button-lock)



(cl-defstruct position file row col)

(defun get-string-from-file (filePath)
  "Return filePath's file content."
  (with-temp-buffer
    (insert-file-contents filePath)
    (buffer-string)))

(defun get-json-from-file (filePath)
  "Return json object from filePath's content"
  (let* ((json-key-type 'string)
	 (str (get-string-from-file filePath)))
    (json-read-from-string str)))

;; Global variable holding the annotations
(defvar liquid-annot-table)

;; -----------------------------------------------------------------------------------------------
;; API for getting annots -- alist
;; -----------------------------------------------------------------------------------------------
;; (setq liquid-annot-table (get-json-from-file "/Users/rjhala/tmp/.liquid/flycheck_Foo.hs.json"))
;; 
;; (defun liquid-annot (table row col)
;;   "Get annotation from table from identifier at row, col"
;;   (let* ((r    (format "%d" row))
;; 	 (c    (format "%d" col))
;; 	 (tys  (assoc "types" table))
;; 	 (ro   (assoc r tys)))
;;     (cdr (assoc "ann" (assoc c ro)))))
;; -----------------------------------------------------------------------------------------------

;; -----------------------------------------------------------------------------------------------
;; API for getting annots -- hash-table 
;; -----------------------------------------------------------------------------------------------

(setq liquid-annot-table 
      (let ((json-object-type 'hash-table))
	(get-json-from-file "/Users/rjhala/tmp/.liquid/flycheck_Foo.hs.json")))

(defun gethash-nil (key table) 
  (if table 
      (gethash key table nil)
      nil))

(defun liquid-annot-get (file row col)
  "Get annotation for identifier at row, col in file"
  (let* ((table (gethash-nil file liquid-annot-table))
	 (r     (format "%d" row))
	 (c     (format "%d" col))
	 (tys   (gethash-nil "types" table))
	 (ro    (gethash-nil r tys)))
    (gethash-nil "ann" (gethash-nil c ro))))

;; -- Display --------------------------------------------------------------

;; If you want the separate balloon-popup
(defun liquid-tip-popup (text)
  "Display text in a window popup"
  (if (and (functionp 'ac-quick-help-use-pos-tip-p)
           (ac-quick-help-use-pos-tip-p))
      (pos-tip-show text 'popup-tip-face nil nil 300 popup-tip-max-width)
    (popup-tip text)))

;; If you just want the ascii-popup
;; (defun liquid-tip-popup (text)
;;  "Display text in ascii popup"
;;   (popup-tip text))


;; -- Compute range ---------------------------------------------------------

(defvar liquid-id-regexp 
  (rx (one-or-more (not (in " \n\t()[]{}")))))

(defun liquid-splitters () 
  '( ?\s  ?\t ?\n ?\( ?\) ?\[ ?\] ))

(defun liquid-is-split (c)
  "Is the character `c` a splitter?"
  (member c (liquid-splitters)))

(defun liquid-id-start-pos (low p)
  "Find the largest position less than `p` that is a splitter"
  (let* ((ch (char-before p)))
     (if (or (<= p low) (liquid-is-split ch)) 
	 p 
         (liquid-id-start-pos low (- p 1)))))


(defun column-number-at-pos (pos)
  "Find the column of position pos"
  (+ (- pos (line-beginning-position)) 1))

(defun start-column-number-at-pos (pos)
  "Find the starting column of identifier at pos"
     (let* ((low   (line-beginning-position))
	    (start (liquid-id-start-pos low pos)))
       (column-number-at-pos start)))

(defsubst liquid-get-position ()
  (save-excursion
    (widen)
    (make-position
     :file (expand-file-name (buffer-file-name))
     :row  (line-number-at-pos)
     :col  (start-column-number-at-pos (point)))))

(defun position-string (pos)
  "position -> string"
  (format "(%s, %s) in [%s]" 
	  (position-row pos) 
	  (position-col pos)
	  (position-file pos)))

;; DEBUG (defun liquid-annot-at-pos-0 (pos)
;; DEBUG   "Info to display: just the file/line/constant string"
;; DEBUG   (let* ((info  (format "hello!")))
;; DEBUG     (format "the information at %s is %s" 
;; DEBUG 	    (position-string pos)
;; DEBUG 	    info)))

;; DEBUG (defun liquid-annot-at-pos-1 (pos)
;; DEBUG   "Info to display: the identifier at the position or NONE" 
;; DEBUG   (let* ((ident (liquid-ident-at-pos pos)))
;; DEBUG     (format "the identifier at %s is %s" 
;; DEBUG 	    (position-string pos) 
;; DEBUG 	    ident)))


(defun liquid-ident-at-pos (pos)
  "Return the identifier at a given position"
  (thing-at-point 'word))

(defun liquid-annot-at-pos-2 (pos)
  "Info to display: type annotation for the identifier at the position or NONE" 
  (let* ((file (position-file pos))
	 (row  (position-row  pos))
	 (col  (position-col  pos)))
    (liquid-annot-get file row col)))

(defun liquid-annot-at-pos (pos)
  "Determine info to display"
  (liquid-annot-at-pos-2 pos))

;;;###autoload
(defun liquid-tip-show ()
  "Popup help about anything at point."
  (interactive)
  (let* ((pos    (liquid-get-position))
	 (ident  (liquid-ident-at-pos pos))
         (annot  (liquid-annot-at-pos pos)))
    (if annot 
	(liquid-tip-popup annot)
        (liquid-tip-popup (format "No annotation for %s at %s" ident (position-string pos))))))


;;;###autoload
(defun liquid-tip-init ()
  "Initialize liquid-tip by making all identifiers buttons"
  (interactive)
  (progn (button-lock-mode 1)
	 (button-lock-set-button liquid-id-regexp 'liquid-tip-show)
	 ;; (button-lock-set-button "yoga" 'liquid-tip-show)
	 ;; (button-lock-set-button "mydiv" 'liquid-tip-show)
	 ))

;;;###autoload
(defun liquid-tip-update ()
  "Update liquid-annot-table by reloading annot file for buffer"
  (interactive)
  42)


;; DEBUG (defface my-tooltip
;; DEBUG   '((t
;; DEBUG      :background "gray85"
;; DEBUG      :foreground "black"
;; DEBUG      :inherit variable-pitch))
;; DEBUG   "Face for my tooltip.")
;; DEBUG 
;; DEBUG (defface my-tooltip-highlight
;; DEBUG   '((t
;; DEBUG      :background "blue"
;; DEBUG      :foreground "white"
;; DEBUG      :inherit my-tooltip))
;; DEBUG   "Face for my tooltip highlighted.")
;; DEBUG 
;; DEBUG (let ((str (propertize "foo\nbar\nbaz" 'face 'my-tooltip)))
;; DEBUG   (put-text-property 6 11 'face 'my-tooltip-highlight str)
;; DEBUG   (pos-tip-show-no-propertize str 'my-tooltip))

(provide 'liquid-tip)

;; Local Variables:
;; coding: utf-8
;; mode: emacs-lisp
;; End:

;;; liquid-tip.el ends here
