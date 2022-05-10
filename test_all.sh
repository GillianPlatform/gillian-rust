for FILE in examples/*.rs; do
  python scripts/test.py $(echo $(basename ${FILE}) | cut -d '.' -f1)
done;