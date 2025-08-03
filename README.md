## Agda Exercises

A collection of exercises to build Agda skills, they are more related to
programming than math since my goal is to use Agda to improve program
correctness.

For every exercise there's the challenge `XXX_Holey.agda` and my best solution
`XXX.agda`. (I'm using Agda version 2.7.0.1)

DISCLAIMER: I'm learning Agda so do not consider my solutions as good solutions
but only as possible solutions 😃.

If you want to: suggest improvements to one or more solutions, better solutions
or more problems, you are more than welcome, open an issue or better submit a
pull request.

Solve the problems in the following order:

1. [EvenOrOdd](./src/EvenOrOdd_Holey.agda)
2. [FizzBuzz](./src/FizzBuzz_Holey.agda)

### How to use this repository

- Clone or fork this repository on your machine
- [Install Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html)
- Fire up Emacs, the following is my config 😁

  ```
  (when (executable-find "agda-mode")
    (let ((coding-system-for-read 'utf-8)
          (agda-mode-source-path (shell-command-to-string "agda-mode locate")))
      (load-file agda-mode-source-path)
      (native-compile-async (list agda-mode-source-path) nil t))

    (with-eval-after-load 'agda2
      (setq agda2-backend "GHC")
      (setq agda2-program-args '("--show-implicit"))

      (defun agda2-align-equality-reasoning-block ()
        "Align proofs in equality reasoning blocks between `begin' and `∎'"
        (interactive)
        (let ((region (if (region-active-p)
                          (cons (region-beginning) (region-end))
                        (cons (point-min) (point-max)))))
          (align-regexp (car region) (cdr region) "\\(\\s-*\\)≡⟨.*⟩$")))

      (defun cc/--setup-agda ()
        "Setup Agda major mode after loading in buffer"
        (keymap-set agda2-mode-map "C-c C-q"
                    (lambda ()
                      (interactive)
                      (dolist (buf (buffer-list))
                        (with-current-buffer buf
                          (when (equal (buffer-name buf) "*Agda information*")
                            (let ((windows (get-buffer-window-list buf)))
                              (dolist (win windows)
                                (delete-window win))))))))

      (add-hook 'agda2-mode-hook #'cc/--setup-agda))))
  ```

- For every problem there's a file in the `src/` directory with suffix
  `_Holey.agda`, open the file, you will find some code and comments to help you
  solve the problem, load the file in Agda (`C-c C-l`), fill the holes and make
  Agda happy. You can find my solution in the same directory.
- Profit 💰
