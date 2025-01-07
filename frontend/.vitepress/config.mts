import { defineConfig } from 'vitepress'

// https://vitepress.dev/reference/site-config
export default defineConfig({
  title: "Type Inference Zoo",
  description: "Type Inference Algorithm Collections",
  themeConfig: {
    // https://vitepress.dev/reference/default-theme-config
    nav: [
      { text: 'Home', link: '/' },
      { text: 'Playground', link: '/playground' },
      { text: 'Reference', link: '/quick-reference' },
      { text: 'Research', link: '/research' },
    ],

    sidebar: [],

    socialLinks: [
      { icon: 'github', link: 'https://github.com/cu1ch3n/type-inference-zoo' }
    ],

    footer: {
      message: 'Released under the <a href="https://github.com/cu1ch3n/type-inference-zoo/blob/main/LICENSE">MIT License</a>.',
      copyright: 'Copyright © 2025 <a href="https://cuichen.cc/">Chen Cui</a>'
    }
  },
  cleanUrls: true
})
