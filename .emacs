(package-initialize)

(load "~/.emacs.d/lisp/PG/generic/proof-site")

(eval-after-load "proof-script" '(progn
                                   (define-key proof-mode-map [(C-down)]
                                     'proof-assert-next-command-interactive)
                                   (define-key proof-mode-map [(C-up)]
                                     'proof-undo-last-successful-command)
				   (define-key proof-mode-map [(C-return)]
                                     'proof-goto-point)
                                   ))

(electric-pair-mode 1)
(show-paren-mode 1)
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(custom-enabled-themes (quote (wombat)))
 '(package-selected-packages (quote (yasnippet)))
 '(proof-three-window-mode-policy (quote hybrid)))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )
