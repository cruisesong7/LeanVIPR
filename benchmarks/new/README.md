# Additional VIPR v1.0 certificates

The certificates in this directory total about 18 GB, so git does not track them.
`manifest.csv` lists each one with its source URL, SHA-256 and size. To download
them into place:

```bash
python3 benchmarks/download_new.py                      # all 112, skips files already present
python3 benchmarks/download_new.py --sets negative chvatal
python3 benchmarks/download_new.py --only acc-0 bell5
python3 benchmarks/download_new.py --verify             # rehash existing files
```

Each file is checked against the manifest before it is moved into
`<set>/<instance>.vipr.gz`. Interrupted downloads stay in `*.part` files and
are retried on the next run.

| Set | Certificates | Source |
|---|---:|---|
| `easy` | 56 | Numerically easy MIPs, [scipopt/vipr experiments](https://github.com/scipopt/vipr/tree/master/experiments) (`http://www.zib.de/gleixner/vipr/`) |
| `hard` | 50 | Numerically difficult MIPs, same source |
| `chvatal` | 3 | Chvátal's conjecture certificates; see `chvatal/SOURCE.md` |
| `negative` | 3 | Forged and manipulated certificates; see `negative/SOURCE.md` |

The `negative` files are plain `.vipr` upstream. The script gzips them, and
their manifest hash is the hash of the uncompressed file.

To check the certificates, run `benchmarks/run_new.py`. Results go to
`benchmarks/results/new_*.csv`.

The C++ reference checker is built locally and git doesn't track it:

```bash
git clone https://github.com/scipopt/vipr.git viprcheck
git -C viprcheck checkout 99eec19
cmake -S viprcheck/code -B viprcheck/code/build -DCMAKE_BUILD_TYPE=Release -DVIPRCOMP=OFF
cmake --build viprcheck/code/build --target viprchk
```
