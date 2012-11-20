set -o errexit
cabal configure
cabal build
for ((;;)) do
    inotifywait -qq --recursive --exclude '(.+~)|(\.#.+)' --event modify Control || true
    cabal build
done
