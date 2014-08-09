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
(require 'flymake)
(require 'eldoc)
(require 'pos-tip nil t)
(require 'log4e)
(require 'yaxception)
(require 'thingatpt)

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


(defvar liquid-annot-table)
(setq liquid-annot-table (get-json-from-file "/Users/rjhala/tmp/.liquid/flycheck_Foo.hs.json"))

(defun liquid-annot (table row col)
  "Get annotation from table from identifier at row, col"
  (let* ((r    (format "%d" row))
	 (c    (format "%d" col))
	 (tys  (assoc "types" table))
	 (ro   (assoc r tys)))
    (cdr (assoc "ann" (assoc c ro)))))

;; If you want the separate balloon-popup
(defun liquid-popup-tip (text)
  (if (and (functionp 'ac-quick-help-use-pos-tip-p)
           (ac-quick-help-use-pos-tip-p))
      (pos-tip-show text 'popup-tip-face nil nil 300 popup-tip-max-width)
    (popup-tip text)))

;; If you just want the ascii-popup
;; (defun liquid-popup-tip (text)
;;   (popup-tip text))


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

(defun liquid-annot-at-pos-0 (pos)
  "Info to display: just the file/line/constant string"
  (let* ((info  (format "hello!")))
    (format "the information at %s is %s" 
	    (position-string pos)
	    info)))

(defun liquid-ident-at-pos (pos)
  "Return the identifier at a given position"
  (thing-at-point 'word))

(defun liquid-annot-at-pos-1 (pos)
  "Info to display: the identifier at the position or NONE" 
  (let* ((ident (liquid-ident-at-pos pos)))
    (format "the identifier at %s is %s" 
	    (position-string pos) 
	    ident)))

(defun liquid-annot-at-pos-2 (pos)
  "Info to display: the identifier at the position or NONE" 
  (let* ((row (position-row pos))
	 (col (position-col pos)))
    (liquid-annot liquid-annot-table row col)))

(defun liquid-annot-at-pos (pos)
  "Determine info to display"
  (liquid-annot-at-pos-2 pos))

;;;###autoload
(defun liquid-annot-popup ()
  "Popup help about anything at point."
  (interactive)
  (let* ((pos    (liquid-get-position))
	 (ident  (liquid-ident-at-pos pos))
         (annot  (liquid-annot-at-pos pos)))
    (if annot 
	(liquid-popup-tip annot)
        (liquid-popup-tip (format "No annotation for: %s" ident)))))

;;; cloned from  tss-popup-help

(provide 'liquid-tip)

;; Local Variables:
;; coding: utf-8
;; mode: emacs-lisp
;; End:

;;; liquid-tip.el ends here
