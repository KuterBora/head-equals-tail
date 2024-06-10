(include-book "std/util/define" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "kestrel/utilities/defthmr" :DIR :SYSTEM)

(set-induction-depth-limit 1)

; Vertex Counters
(defun vertex-count (tree)
  (if (atom tree)
    1
    (+ 1
       (vertex-count (car tree))
       (vertex-count (cdr tree)))))

(defun sum-vertex-count (tree-list)
  (if (consp tree-list)
    (+ (vertex-count (car tree-list))
       (sum-vertex-count (cdr tree-list)))
    0))

; H-tree Defintion / Helpers
(defun make-htree (l r)
  (list l r))

(defun htree-p (ht)
  (or (stringp ht)
      (and (true-listp ht)
           (= (length ht) 2)
           (and (or (htree-p (car ht)) (stringp (car ht)))
                (or (htree-p(cadr ht)) (stringp (cadr ht)))))))

(defthm test-htree-p
  (and (htree-p (make-htree "A" (make-htree (make-htree "B" (make-htree "C" "D")) "R")))
       (htree-p "a")
       (htree-p '("a" "b"))
       (not (htree-p nil))
       (not (htree-p '("a" nil)))
       (not (htree-p '("a" "b" "c")))))

(defthm car-of-htree
  (implies (and (htree-p ht) (consp ht))
           (htree-p (car ht))))

(defthm cadr-of-htree
  (implies (and (htree-p ht) (consp ht))
           (htree-p (cadr ht))))

; Lists of Htree
(defun htree-list-p (lst)
  (if (atom lst) (not lst)
    (and (htree-p (car lst))
     (htree-list-p (cdr lst)))))

(defthm true-listp-when-htree-list-p
  (implies (htree-list-p hts)
       (true-listp hts)))

(defthm car-when-htree-list-p
  (implies (and hts (htree-list-p hts))
       (htree-p (car hts))))

(defthm cdr-when-htree-list-p
  (implies (htree-list-p hts)
       (htree-list-p (cdr hts))))

(defthm htree-list-p-of-append
  (implies (and (htree-list-p hts1) (htree-list-p hts2))
       (htree-list-p (append hts1 hts2))))

; path-p: recognizer for paths in an htree
;   A path is a list of 0s and 1s.
;   Optionally, the last element may be a string.
;   Including a search string as the last element lets us distinguish
;   between a return value of nil when there are no occurrences of
;   the search string in the htree, and when the htree is just the
;   string.
(defun path-p (x)
  (or (not x)
      (and (consp x)
       (or (and (stringp (car x)) (not (cdr x)))
           (and (or (equal (car x) 0) (equal (car x) 1))
            (path-p (cdr x)))))))

(defun path-endp (x)
  (or (atom x)
      (and (stringp (car x)) (atom (cdr x)))))

; unstrung-path-p
;   The optional string at the end of a path-p can be a nuisance
;   when reasoning about an in-progress search.  unstrung-path-p
;   recognizes path-p values that don't end with a string.
(defun unstrung-path-p (x)
  (or (not x)
      (and (consp x)
       (or (equal (car x) 0) (equal (car x) 1))
       (unstrung-path-p (cdr x)))))

(defthm unstrung-path-p-of-cons-0
  (implies (unstrung-path-p x)
       (unstrung-path-p (cons 0 x))))

(defthm unstrung-path-p-of-cons-1
  (implies (unstrung-path-p x)
       (unstrung-path-p (cons 1 x))))

(defthm path-p-when-unstrung-path-p
  (implies (unstrung-path-p x)
       (path-p x)))

(defun path-order (path1 path2)
  (cond ((and (path-endp path1) (path-endp path2)) 0)
    ((path-endp path1) -1)
    ((path-endp path2)  1)
    ((and (integerp (car path1)) (integerp (car path2)))
     (cond
       ((< (car path1) (car path2)) -1)
       ((< (car path2) (car path1))  1)
       (t (path-order (cdr path1) (cdr path2)))))
    (t nil)))

(defthm path-p-of-append
  (implies (and (unstrung-path-p path1) (path-p path2))
       (path-p (append path1 path2))))

(defthm unstrung-path-p-of-append
  (implies (and (unstrung-path-p path1)
        (unstrung-path-p path2))
       (unstrung-path-p (append path1 path2))))

(defthm unstrung-path-p-of-rev
  (implies (unstrung-path-p x)
       (unstrung-path-p (rev x))))

; List of Unstrung Paths
(defun unstrung-path-list-p (lst)
  (if (atom lst) (not lst)
    (and (unstrung-path-p (car lst))
     (unstrung-path-list-p (cdr lst)))))

(defthm true-listp-when-unstrung-path-list-p
  (implies (unstrung-path-list-p path)
       (true-listp path)))

(defthm car-when-unstrung-path-list-p
  (implies (and path (unstrung-path-list-p path))
       (unstrung-path-p (car path))))

(defthm cdr-when-unstrung-path-list-p
  (implies (unstrung-path-list-p path)
       (unstrung-path-list-p (cdr path))))

; Fetch Subtree
(defun fetch-subtree (ht path)
  (cond ((path-endp path) ht)
    ((atom ht) nil)
    ((equal (car path) 0) (fetch-subtree (car ht) (cdr path)))
    ((equal (car path) 1) (fetch-subtree (cadr ht) (cdr path)))
    (t (er hard 'fetch-subtree "bad path: ~x0." path))))

(defthm test-fetch-subtree
  (let ((HTMAGIC (make-htree "A" (make-htree (make-htree "B" (make-htree "C" "D")) "R"))))
    (and (equal (fetch-subtree HTMAGIC nil) HTMAGIC)
         (equal (fetch-subtree HTMAGIC '(1)) (make-htree (make-htree "B" (make-htree "C" "D")) "R"))
         (equal (fetch-subtree HTMAGIC '(1 0)) (make-htree "B" (make-htree "C" "D")))
         (equal (fetch-subtree HTMAGIC '(1 0 1)) (make-htree "C" "D"))
         (equal (fetch-subtree HTMAGIC '(0)) "A")
         (equal (fetch-subtree HTMAGIC '(1 0 0)) "B")
         (equal (fetch-subtree HTMAGIC '(1 0 1 0)) "C")
         (equal (fetch-subtree HTMAGIC '(1 0 1 1)) "D")
         (equal (fetch-subtree HTMAGIC '(1 1)) "R"))))

(defthm fetch-subtree-of-append
  (implies
    (unstrung-path-p path1)
    (equal (fetch-subtree ht (append path1 path2))
       (fetch-subtree (fetch-subtree ht path1) path2))))

; Head Search
(defun head-search (h st) 
  (if (atom h) 
    (and (equal h st) (cons st nil))
    (let ((left (head-search (car h) st)))
      (or (and left (cons 0 left))
 (let ((right (head-search (cadr h) st)))
   (and right (cons 1 right)))))))

(defthm test-head-search
  (let ((HTMAGIC (make-htree "A" (make-htree (make-htree "B" (make-htree "C" "D")) "R"))))
    (and (equal (head-search "A" "A") (cons "A" nil))
         (equal (head-search "A" "B") nil)
         (equal (head-search HTMAGIC "A") '(0 "A"))
         (equal (head-search HTMAGIC "R") '(1 1 "R"))
         (equal (head-search HTMAGIC "B") '(1 0 0 "B"))
         (equal (head-search HTMAGIC "C") '(1 0 1 0 "C"))
         (equal (head-search HTMAGIC "D") '(1 0 1 1 "D"))
         (equal (head-search HTMAGIC "E") nil))))

(defthm path-p-of-head-search
 (implies (stringp st)
       (path-p (head-search h st))))

(defthm fetch-subtree-of-head-search
  (let ((path (head-search ht str)))
    (implies (and path (stringp str))
         (equal (fetch-subtree ht path) str))))

(defthm head-search-finds-path
  (implies
    (and (stringp st)
         (head-search ht st))
    (equal (fetch-subtree ht (head-search ht st)) st)))

(defthm head-search-finds-least-path
  (implies
    (and (stringp str)
     (path-p path)
     (equal (fetch-subtree ht path) str))
    (and (head-search ht str)
        (<= (path-order (head-search ht str) path) 0))))

; Predicates for HTS and PTS
(defun hts-pts-ok (hts pts root)
  (cond
    ((and (endp hts) (endp pts)) t)
    ((or  (endp hts) (endp pts)) nil)
    (t (and (equal (car hts) (fetch-subtree root (car pts)))
        (hts-pts-ok (cdr hts) (cdr pts) root)))))

(defun fetch-hts (root path)
  (cond
   ((or (atom path) (endp root)) nil)
   ((equal (car path) 1)
    (fetch-hts (cadr root) (cdr path)))
   ((equal (car path) 0)
    (append (fetch-hts (car root) (cdr path))
          (cons (cadr root) nil)))))

(defthm test-fetch-hts
  (let ((HTMAGIC (make-htree "A" (make-htree (make-htree "B" (make-htree "C" "D")) "R"))))
    (and (equal (fetch-hts HTMAGIC nil) nil)
         (equal (fetch-hts  HTMAGIC '(0)) (list (make-htree (make-htree "B" (make-htree "C" "D")) "R")))
         (equal (fetch-hts  HTMAGIC '(1)) nil)
         (equal (fetch-hts  HTMAGIC '(1 1)) nil)
         (equal (fetch-hts  HTMAGIC '(1 0)) '("R"))
         (equal (fetch-hts  HTMAGIC '(1 0 0)) (list (make-htree "C" "D") "R"))
         (equal (fetch-hts  HTMAGIC '(1 0 1)) (list "R"))
         (equal (fetch-hts  HTMAGIC '(1 0 1 0)) (list "D" "R"))
         (equal (fetch-hts  HTMAGIC '(1 0 1 1)) (list "R")))))

; Tail Search
(defun tail-search* (ht str hts pts path)
  (declare (xargs :measure (+ (vertex-count ht) (sum-vertex-count hts))))
  (if (atom ht)
    (if (equal ht str)
      (append path (cons ht nil))
      (if (> (+ (vertex-count ht) (sum-vertex-count hts)) 1)
        (tail-search* (car hts) str (cdr hts) (cdr pts) (car pts))
        nil))
    (tail-search* (car ht) str (cons (cadr ht) hts) (cons (append path (cons 1 nil)) pts) (append path (cons 0 nil)))))

(defun tail-search (ht str)
  (tail-search* ht str nil nil nil))

(defthm test-tail-search
  (let ((HTMAGIC (make-htree "A" (make-htree (make-htree "B" (make-htree "C" "D")) "R"))))
    (and (equal (tail-search "A" "A") (cons "A" nil))
         (equal (tail-search "A" "B") nil)
         (equal (tail-search HTMAGIC "A") '(0 "A"))
         (equal (tail-search HTMAGIC "R") '(1 1 "R"))
         (equal (tail-search HTMAGIC "B") '(1 0 0 "B"))
         (equal (tail-search HTMAGIC "C") '(1 0 1 0 "C"))
         (equal (tail-search HTMAGIC "D") '(1 0 1 1 "D"))
         (equal (tail-search HTMAGIC "E") nil))))

(defthm path-p-of-tail-search*
  (implies (and (stringp str)
        (unstrung-path-list-p pts)
        (unstrung-path-p path))
           (path-p (tail-search* ht str hts pts path))))

(defthm path-p-of-tail-search
  (implies (stringp str)
           (path-p (tail-search ht str))))

(defthm fetch-subtree-tail-search*
  (let ((path2 (tail-search* ht str hts pts path)))
    (implies (and path2
                  (equal ht (fetch-subtree root path))
                  (stringp str)
                  (unstrung-path-list-p pts)
                  (unstrung-path-p path)
                  (hts-pts-ok hts pts root))
             (equal (fetch-subtree root path2) str)))
  :hints(("Goal" :induct (tail-search* ht str hts pts path))))

(defthm fetch-subtree-tail-search
  (let ((path2 (tail-search ht str)))
    (implies (and path2
                  (stringp str))
             (equal (fetch-subtree ht path2) str))))

; Tail Search with Good Args
(defun tail-search-good-args (root ht hts pts path)
  (and (htree-p ht)
       (unstrung-path-p path)
       (unstrung-path-list-p pts)
       (htree-list-p hts)
       (hts-pts-ok hts pts root)
       (equal ht (fetch-subtree root path))
       ;(equal hts (fetch-hts root path))
       ))

; Lemmas for Args Stay Good
(defthm htree-made-of-htree
  (implies (and (htree-p ht) (consp ht))
           (and (htree-p (car ht)) (htree-p (cadr ht)))))

(defthm car-of-fetch-subtree
  (implies (and (htree-p (fetch-subtree root path))
              (unstrung-path-p path))
         (equal (car (fetch-subtree root path))
                (fetch-subtree (fetch-subtree root path)
                               '(0)))))

(defthm htree-p-of-fetch-subtree
  (implies (and (htree-p ht)
              (unstrung-path-p path)
              (consp ht))
         (htree-p (fetch-subtree ht '(0)))))

(defthm fetch-hts-append-0
  (implies (and (htree-p (fetch-subtree root path)) (consp (fetch-subtree root path))
              (unstrung-path-p path) )
         (equal (cons (cadr (fetch-subtree root path))
                      (fetch-hts root path))
                (fetch-hts root (append path '(0))))))

(defthm cadr-of-fetch-subtree
  (implies (and (htree-p (fetch-subtree root path)) (consp (fetch-subtree root path))
             (unstrung-path-p path) )
           (equal (fetch-subtree (fetch-subtree root path)'(1)) 
                 (cadr (fetch-subtree root path)))))

(defthm htree-list-p-of-fetch-hts
  (implies (and (htree-p root) (unstrung-path-p path))
           (htree-list-p (fetch-hts root path))))

(defthm args-stay-good-1
  (implies (and (tail-search-good-args root ht hts pts path) (consp ht) (htree-p root)) 
           (tail-search-good-args root (car ht) (cons (cadr ht) hts) (cons (append path (list 1)) pts) (append path (list 0))))
  :hints (("Goal" :in-theory (disable  fetch-hts-append-0))
          ("Goal''" :in-theory (enable  fetch-hts-append-0))))

; starts failing here with fetch-hts in good args

(defthm args-stay-good-2
  (implies (and (tail-search-good-args root ht hts pts path) (atom ht) (consp hts) (htree-p root))
           (tail-search-good-args root (car hts) (cdr hts) (cdr pts) (car pts))))

; Tail-Searchx
(define tail-searchx (htree ht str hts pts path)
  :measure (+ (vertex-count ht) (sum-vertex-count hts))
  :hints (("Goal":in-theory (disable tail-search-good-args)))
  :verify-guards nil
  (and (tail-search-good-args htree ht hts pts path)
     (if (atom ht)
         (if (equal ht str)
           (append path (list ht))
           (if (consp hts)
             (tail-searchx htree (car hts) str (cdr hts) (cdr pts) (car pts))
             nil))
         (tail-searchx htree (car ht) str (cons (cadr ht) hts) (cons (append path (cons 1 nil)) pts) (append path (cons 0 nil))))))

(in-theory (enable tail-searchx))

(defun tail-searchxx (ht str)
  (tail-searchx ht ht str nil nil nil))

(defthm test-tail-searchx
  (let ((HTMAGIC (make-htree "A" (make-htree (make-htree "B" (make-htree "C" "D")) "R"))))
    (and (equal (tail-searchxx "A" "A") (cons "A" nil))
         (equal (tail-searchxx "A" "B") nil)
         (equal (tail-searchxx HTMAGIC "A") '(0 "A"))
         (equal (tail-searchxx HTMAGIC "R") '(1 1 "R"))
         (equal (tail-searchxx HTMAGIC "B") '(1 0 0 "B"))
         (equal (tail-searchxx HTMAGIC "C") '(1 0 1 0 "C"))
         (equal (tail-searchxx HTMAGIC "D") '(1 0 1 1 "D"))
         (equal (tail-searchxx HTMAGIC "E") nil))))

(defthm path-p-of-tail-searchx
  (implies (and (stringp str)
                (tail-search-good-args root ht hts pts path))
           (path-p (tail-searchx root ht str hts pts path)))
   :hints (("Goal" :induct (tail-searchx root ht str hts pts path))))

(defthm fetch-subtree-tail-searchx
  (let ((path2 (tail-searchx root ht str hts pts path)))
    (implies (and path2
          (equal ht (fetch-subtree root path))
          (stringp str)
          (unstrung-path-list-p pts)
          (unstrung-path-p path)
          (hts-pts-ok hts pts root))
         (equal (fetch-subtree root path2) str)))
  :hints(("Goal" :induct (tail-searchx root ht str hts pts path))))

; Trying to show tail search will be true if str is in hts, this attempt did not work
(defthm tail-search*-first-recursion
  (let ((path2 (tail-search* ht str hts pts path))
        (path3 (tail-search* (car ht) str (cons (cadr ht) hts) (cons (append path (list 1)) pts) (append path (list 0)))))
    (implies (and path3
                  (stringp str)
                  (tail-search-good-args ht ht hts pts path))
             path2))
  :hints (("Goal" :induct (tail-search* ht str hts pts path))))

(defthm tail-search*-second-rescursion
  (let ((path2 (tail-search* ht str hts pts path))
        (path3 (tail-search* (car hts) str (cdr hts) (cdr pts) (car pts))))
    (implies (and path3
                  (stringp str)
                  (atom ht)
                  (tail-search-good-args ht ht hts pts path))
             path2))
  :hints (("Goal" :induct (tail-search* ht str hts pts path))))

; Mark's Latest Idea
(defun prefixes-of-path (path pts)
  (if (endp pts) t
    (or (prefixp path (car pts))
        (prefixes-of-path path (cdr pts)))))

(defthm prefixes-of-path-of-cons
  (implies (and (prefixes-of-path path pts)
                (prefixp new-pt path))
           (prefixes-of-path path (cons new-pt pts))))

(defun tail-findable (hts str)
  (if (endp hts) nil
    (or (head-search (car hts) str)
        (tail-findable (cdr hts) str))))

(set-induction-depth-limit 2)
(defthm lemma-findable
  (implies
    (and (unstrung-path-p path)
         (unstrung-path-list-p pts)
         (tail-findable (cons ht hts) str))
    (tail-search* ht str hts pts path)))
(set-induction-depth-limit 1)

(defthm tail-search-iff-head-search
  (implies (stringp str)
           (iff (head-search root str)
                (tail-search root str)))
  :hints(("Goal"
    :in-theory (disable head-search-finds-least-path)
   :use((:instance head-search-finds-least-path
                    (ht root)
                    (path (tail-search root str)))))))

(defthm tail-search-finds-path
  (implies
    (and (stringp str)
     (unstrung-path-p path)
     (equal (fetch-subtree ht path) str))
    (tail-search ht str)))

; Last Attempts

(defthm unstrung-path-equality
  (implies (and (unstrung-path-p path1)
                (unstrung-path-p path2)
                (<= (path-order path1 path2) 0)
                (<= (path-order path2 path1) 0)
                )
           (equal path1 path2))
  :rule-classes NIL)

(defun unstrung (path) 
  (rev (cdr (rev path)))
 )

(defthm path-to-unstrung-path
  (implies (path-p path)
           (unstrung-path-p (unstrung path))))

(defthm unstrung-head-equals-tail-with-assumptions
    (implies (and (stringp st)
                  (unstrung-path-p (unstrung (head-search ht st)))
                  (unstrung-path-p (unstrung (tail-search ht st)))
                  (<= (path-order (unstrung (tail-search ht st))
                                  (unstrung (head-search ht st))) 0)
                  (<= (path-order (unstrung (head-search ht st)) 
                                  (unstrung (tail-search ht st))) 0))
             (equal (unstrung (head-search ht st)) 
                    (unstrung (tail-search ht st))))
    :hints (("Goal" :use ((:instance unstrung-path-equality
                         (path1 (unstrung (tail-search ht st)))
                         (path2 (unstrung (head-search ht st))))))))

(defthm head-search-iff-least-path
  (implies
   (and (stringp str)
        (unstrung-path-p path)
        (equal (fetch-subtree ht path) str))
   (<= (path-order (unstrung (head-search ht str)) path) 0)))

  
(defthm head-search-less-than-tail-search
  (implies
   (and (stringp st)
        (unstrung-path-p (unstrung (tail-search ht st)))
        (equal (fetch-subtree ht (unstrung (tail-search ht st))) st))
   (<= (path-order (unstrung (head-search ht st)) (unstrung (tail-search ht st))) 0))
  :hints (("Goal" :use ((:instance head-search-iff-least-path
                         (ht ht)
                         (str st)
                         (path (unstrung (tail-search ht st))))))))

(defthmr unstrung-head-equals-tail
  (let ((head-result (unstrung (head-search ht st)))
        (tail-result (unstrung (tail-search ht st))))
    (implies (and (stringp st)
                  (<= (path-order tail-result head-result) 0)
                  (equal (fetch-subtree ht tail-result) st))
             (and (equal head-result tail-result))))
  :hints (("Goal" 
           :use ((:instance unstrung-head-equals-tail-with-assumptions
                  (st st)
                  (ht ht))
                 (:instance path-to-unstrung-path
                  (path (head-search ht st)))
                 (:instance path-to-unstrung-path
                  (path (tail-search ht st)))
                 (:instance head-search-less-than-tail-search
                  (st st)
                  (ht ht))))))#|ACL2s-ToDo-Line|#
