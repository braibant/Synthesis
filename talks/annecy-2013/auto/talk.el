(TeX-add-style-hook "talk"
 (lambda ()
    (LaTeX-add-environments
     "remark"
     "twolistings")
    (TeX-add-symbols
     '("behaviors" 1)
     '("parenthesis" 1)
     '("denote" 1)
     '("redbf" 1)
     '("bluebf" 1)
     '("redemph" 1)
     '("bluemph" 1)
     "fesi"
     "rebind"
     "arrow")
    (TeX-run-style-hooks
     "lstocaml"
     "lstcoq"
     "graphicx"
     "listings"
     "mathpartir"
     "amsthm"
     "amssymb"
     "amsmath"
     "iwona"
     "xcolor"
     "babel"
     "english"
     "txfonts"
     "inputenc"
     "utf8"
     "latex2e"
     "beamer10"
     "beamer"
     "9pt")))

