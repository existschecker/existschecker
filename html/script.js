function scrollIfNeeded(element, container) {
  const elRect = element.getBoundingClientRect();
  const contRect = container.getBoundingClientRect();

  // element が container の表示範囲内に完全に収まっているか
  if (elRect.top < contRect.top || elRect.bottom > contRect.bottom) {
    element.scrollIntoView({ behavior: 'smooth', block: 'center' });
  }
}

// ページ上の全ての block-header をフラット配列にする
const allHeaders = Array.from(document.querySelectorAll('.block-header'));
let selectedIndex = 0;

// 初期選択
if (allHeaders.length > 0) {
  allHeaders[selectedIndex].classList.add('selected');
}

document.addEventListener('click', (e) => {
  if (e.target.matches('.toggle')) {
    const btn = e.target;
    const header = btn.closest('.block-header');
    if (!header) return;
    const content = header.nextElementSibling;
    if (!content || !content.classList.contains('block-content')) return;
    content.classList.toggle('collapsed');
    btn.textContent = content.classList.contains('collapsed') ? '▶' : '▼';
    MathJax.typesetPromise();
  }
  const header = e.target.closest('.block-header');
  if (header) {
    // 前の選択を解除
    allHeaders.forEach(h => h.classList.remove('selected'));
    header.classList.add('selected');

    // 配列のインデックスを同期
    selectedIndex = allHeaders.indexOf(header);

    // infoPanel 更新
    const context_vars = header.nextElementSibling.innerHTML;
    const context_formulas = header.nextElementSibling.nextElementSibling.innerHTML;
    infoContent.innerHTML = `Clicked line: ${header.innerHTML}<br>context.vars: ${context_vars}<br>context.formulas: ${context_formulas}`;
    MathJax.typesetPromise();
  }
});

document.addEventListener('keydown', (e) => {
  if (e.key !== 'ArrowDown' && e.key !== 'ArrowUp') return;
  e.preventDefault(); // スクロールを止める

  if (allHeaders.length === 0) return;

  let targetIndex = selectedIndex;

  if (e.ctrlKey) {
    if (e.key === 'ArrowUp') {
      // 親をたどってトップノードを見つける
      let block = allHeaders[selectedIndex].closest('.block');
      while (block.parentElement.closest('.block')) {
        block = block.parentElement.closest('.block');
      }
      const topHeader = block.querySelector('.block-header');
      if (allHeaders[selectedIndex] === topHeader) {
        // すでにトップノードなら、1つ前のトップノードへ
        let prevBlock = block.previousElementSibling;
        while (prevBlock && !prevBlock.querySelector('.block-header')) {
          prevBlock = prevBlock.previousElementSibling;
        }
        if (prevBlock) {
          targetIndex = allHeaders.indexOf(prevBlock.querySelector('.block-header'));
        } else {
          targetIndex = selectedIndex; // 最初のトップノードなら移動なし
        }
      } else {
        // 親をたどってトップノードに移動
        targetIndex = allHeaders.indexOf(topHeader);
      }
    } else if (e.key === 'ArrowDown') {
      // 親をたどってトップノードを見つける
      let block = allHeaders[selectedIndex].closest('.block');
      while (block.parentElement.closest('.block')) {
        block = block.parentElement.closest('.block');
      }
      // 次のトップノードがあれば移動
      const nextTopBlock = block.nextElementSibling;
      if (nextTopBlock) {
        targetIndex = allHeaders.indexOf(nextTopBlock.querySelector('.block-header'));
      }
    }
  } else {
    // 通常の上下移動
    if (e.key === 'ArrowDown') {
      targetIndex = Math.min(selectedIndex + 1, allHeaders.length - 1);
    } else if (e.key === 'ArrowUp') {
      targetIndex = Math.max(selectedIndex - 1, 0);
    }
  }

  if (targetIndex === selectedIndex) return; // 移動先が同じなら何もしない

  // 選択更新
  allHeaders[selectedIndex].classList.remove('selected');
  selectedIndex = targetIndex;
  const header = allHeaders[selectedIndex];
  header.classList.add('selected');

  const proofContainer = document.querySelector('.proof'); // スクロールコンテナ
  scrollIfNeeded(header, proofContainer);

  // infoPanel 更新
  const context_vars = header.nextElementSibling.innerHTML;
  const context_formulas = header.nextElementSibling.nextElementSibling.innerHTML;
  infoContent.innerHTML = `Selected line: ${header.innerHTML}<br>context.vars: ${context_vars}<br>context.formulas: ${context_formulas}`;
  MathJax.typesetPromise();
});

document.getElementById('expandAll').addEventListener('click', () => {
  document.querySelectorAll('.block-content').forEach(c => c.classList.remove('collapsed'));
  document.querySelectorAll('.toggle').forEach(b => b.textContent='▼');
  MathJax.typesetPromise();
});
document.getElementById('collapseAll').addEventListener('click', () => {
  document.querySelectorAll('.block-content').forEach(c => c.classList.add('collapsed'));
  document.querySelectorAll('.toggle').forEach(b => b.textContent='▶');
});
